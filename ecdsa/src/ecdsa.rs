use super::integer::{IntegerChip, IntegerConfig};
use crate::halo2;
use crate::integer;
use crate::maingate;
use ecc::halo2::circuit::Layouter;
use ecc::integer::Range;
use ecc::maingate::RegionCtx;
use ecc::{AssignedPoint, EccConfig, GeneralEccChip};
use halo2::arithmetic::CurveAffine;
use halo2::halo2curves::ff::PrimeField;
use halo2::{circuit::Value, plonk::Error};
use integer::rns::Integer;
use integer::{AssignedInteger, IntegerInstructions};
use maingate::{MainGateConfig, RangeConfig};

#[derive(Clone, Debug)]
pub struct EcdsaConfig {
    pub main_gate_config: MainGateConfig,
    pub range_config: RangeConfig,
}

impl EcdsaConfig {
    pub fn new(range_config: RangeConfig, main_gate_config: MainGateConfig) -> Self {
        Self {
            range_config,
            main_gate_config,
        }
    }

    pub fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub fn integer_chip_config(&self) -> IntegerConfig {
        IntegerConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }
}

#[derive(Clone, Debug)]
pub struct EcdsaSig<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub r: Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    pub s: Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct AssignedEcdsaSig<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub r: AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    pub s: AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct AssignedPublicKey<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub point: AssignedPoint<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct EcdsaChip<
    E: CurveAffine,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
>(GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>);

impl<E: CurveAffine, N: PrimeField, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn new(ecc_chip: GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>) -> Self {
        Self(ecc_chip)
    }

    pub fn scalar_field_chip(
        &self,
    ) -> &IntegerChip<E::ScalarExt, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.0.scalar_field_chip()
    }

    fn ecc_chip(&self) -> GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.0.clone()
    }
}

impl<E: CurveAffine, N: PrimeField, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn verify(
        &self,
        public_key: Value<E>,
        signature: Value<(E::Scalar, E::Scalar)>,
        msg_hash: Value<E::Scalar>,

        aux_generator: E,
        window_size: usize,
        layouter: &mut impl Layouter<N>,
    ) -> Result<(), Error> {
        let mut ecc_chip = self.ecc_chip();

        layouter.assign_region(
            || "assign aux values",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                ecc_chip.assign_aux_generator(ctx, Value::known(aux_generator))?;
                ecc_chip.assign_aux(ctx, window_size, 2)?;
                Ok(())
            },
        )?;

        let scalar_chip = ecc_chip.scalar_field_chip();
        let base_chip = ecc_chip.base_field_chip();

        let (pk, h) = layouter.assign_region(
            || "region 0",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let r = signature.map(|signature| signature.0);
                let s = signature.map(|signature| signature.1);
                let integer_r = ecc_chip.new_unassigned_scalar(r);
                let integer_s = ecc_chip.new_unassigned_scalar(s);
                let msg_hash = ecc_chip.new_unassigned_scalar(msg_hash);

                let r_assigned = scalar_chip.assign_integer(ctx, integer_r, Range::Remainder)?;
                let s_assigned = scalar_chip.assign_integer(ctx, integer_s, Range::Remainder)?;
                let sig = AssignedEcdsaSig {
                    r: r_assigned,
                    s: s_assigned,
                };

                let pk_in_circuit = ecc_chip.assign_point(ctx, public_key)?;
                let pk_assigned = AssignedPublicKey {
                    point: pk_in_circuit,
                };
                let msg_hash = scalar_chip.assign_integer(ctx, msg_hash, Range::Remainder)?;
                // 1. check 0 < r, s < n

                // since `assert_not_zero` already includes a in-field check, we can just
                // call `assert_not_zero`
                scalar_chip.assert_not_zero(ctx, &sig.r)?;
                scalar_chip.assert_not_zero(ctx, &sig.s)?;

                // 2. w = s^(-1) (mod n)
                let (s_inv, _) = scalar_chip.invert(ctx, &sig.s)?;

                // 3. u1 = m' * w (mod n)
                let u1 = scalar_chip.mul(ctx, &msg_hash, &s_inv)?;

                // 4. u2 = r * w (mod n)
                let u2 = scalar_chip.mul(ctx, &sig.r, &s_inv)?;

                // 5. compute Q = u1*G + u2*pk
                let e_gen = ecc_chip.assign_point(ctx, Value::known(E::generator()))?;
                let pairs = vec![(e_gen, u1), (pk_assigned.point.clone(), u2)];
                let q = ecc_chip.mul_batch_1d_horizontal(ctx, pairs, 4)?;

                // 6. reduce q_x in E::ScalarExt
                // assuming E::Base/E::ScalarExt have the same number of limbs
                let q_x = q.x();
                let q_x_reduced_in_q = base_chip.reduce(ctx, q_x)?;
                let q_x_reduced_in_r = scalar_chip.reduce_external(ctx, &q_x_reduced_in_q)?;

                // 7. check if Q.x == r (mod n)
                // scalar_chip.assert_strict_equal(ctx, &q_x_reduced_in_r, &sig.r)?;
                println!("calling...");
                let is_equal = scalar_chip.is_advice_equal_to_instance(
                    ctx,
                    &q_x_reduced_in_r,
                    NUMBER_OF_LIMBS * 3,
                )?;
                let pk_norm = ecc_chip.normalize(ctx, &pk_assigned.point)?;
                Ok((pk_norm, msg_hash))
            },
        )?;

        ecc_chip.expose_public(layouter.namespace(|| "public_key"), pk, 0)?;
        scalar_chip.expose_public(layouter.namespace(|| "hash"), h, NUMBER_OF_LIMBS * 2)?;
        // scalar_chip.expose_public(layouter.namespace(|| "is_equal"), e, NUMBER_OF_LIMBS * 4)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::EcdsaChip;
    use crate::halo2;
    use crate::maingate;
    use ecc::integer::rns::Integer;
    use ecc::integer::rns::Rns;
    use ecc::integer::NUMBER_OF_LOOKUP_LIMBS;
    use ecc::maingate::big_to_fe;
    use ecc::maingate::fe_to_big;
    use ecc::Point;
    use ecc::{EccConfig, GeneralEccChip};
    use halo2::arithmetic::CurveAffine;
    use halo2::circuit::{Layouter, SimpleFloorPlanner, Value};
    use halo2::halo2curves::{
        ff::{Field, FromUniformBytes, PrimeField},
        group::{Curve, Group},
    };
    use halo2::plonk::{Circuit, ConstraintSystem, Error};
    use maingate::mock_prover_verify;
    use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions};
    use num_traits::One;
    use rand_core::OsRng;
    use std::marker::PhantomData;
    use std::rc::Rc;

    const BIT_LEN_LIMB: usize = 68;
    const NUMBER_OF_LIMBS: usize = 4;

    #[derive(Clone, Debug)]
    struct TestCircuitEcdsaVerifyConfig {
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
    }
    #[allow(clippy::type_complexity)]
    fn setup<
        C: CurveAffine,
        N: PrimeField,
        const NUMBER_OF_LIMBS: usize,
        const BIT_LEN_LIMB: usize,
    >(
        k_override: u32,
    ) -> (
        Rns<C::Base, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        Rns<C::Scalar, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        u32,
    ) {
        let (rns_base, rns_scalar) = GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
        let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;
        let mut k: u32 = (bit_len_lookup + 1) as u32;
        if k_override != 0 {
            k = k_override;
        }
        (rns_base, rns_scalar, k)
    }

    impl TestCircuitEcdsaVerifyConfig {
        pub fn new<C: CurveAffine, N: PrimeField>(meta: &mut ConstraintSystem<N>) -> Self {
            let (rns_base, rns_scalar) =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
            let main_gate_config = MainGate::<N>::configure(meta);
            let mut overflow_bit_lens: Vec<usize> = vec![];
            overflow_bit_lens.extend(rns_base.overflow_lengths());
            overflow_bit_lens.extend(rns_scalar.overflow_lengths());
            let composition_bit_lens = vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS];

            let range_config = RangeChip::<N>::configure(
                meta,
                &main_gate_config,
                composition_bit_lens,
                overflow_bit_lens,
            );
            TestCircuitEcdsaVerifyConfig {
                main_gate_config,
                range_config,
            }
        }

        pub fn ecc_chip_config(&self) -> EccConfig {
            EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
        }

        pub fn config_range<N: PrimeField>(
            &self,
            layouter: &mut impl Layouter<N>,
        ) -> Result<(), Error> {
            let range_chip = RangeChip::<N>::new(self.range_config.clone());
            range_chip.load_table(layouter)?;

            Ok(())
        }
    }

    #[derive(Default, Clone)]
    struct TestCircuitEcdsaVerify<E: CurveAffine, N: PrimeField> {
        public_key: Value<E>,
        signature: Value<(E::Scalar, E::Scalar)>,
        msg_hash: Value<E::Scalar>,

        aux_generator: E,
        window_size: usize,
        _marker: PhantomData<N>,
    }

    impl<E: CurveAffine, N: PrimeField> Circuit<N> for TestCircuitEcdsaVerify<E, N> {
        type Config = TestCircuitEcdsaVerifyConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
            TestCircuitEcdsaVerifyConfig::new::<E, N>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<N>,
        ) -> Result<(), Error> {
            let ecc_chip = GeneralEccChip::<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(
                config.ecc_chip_config(),
            );
            let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());
            let _ = ecdsa_chip.verify(
                self.public_key,
                self.signature,
                self.msg_hash,
                self.aux_generator,
                self.window_size,
                &mut layouter,
            );

            config.config_range(&mut layouter)?;

            Ok(())
        }
    }

    #[test]
    fn test_ecdsa_verifier() {
        fn mod_n<C: CurveAffine>(x: C::Base) -> C::Scalar {
            let x_big = fe_to_big(x);
            big_to_fe(x_big)
        }

        fn run<C: CurveAffine, N: FromUniformBytes<64> + Ord>() {
            let g = C::generator();

            // Generate a key pair
            let sk = <C as CurveAffine>::ScalarExt::random(OsRng);
            let public_key = (g * sk).to_affine();

            // Generate a valid signature
            // Suppose `m_hash` is the message hash
            let msg_hash = <C as CurveAffine>::ScalarExt::random(OsRng);

            // Draw arandomness
            let k = <C as CurveAffine>::ScalarExt::random(OsRng);
            let k_inv = k.invert().unwrap();

            // Calculate `r`
            let r_point = (g * k).to_affine().coordinates().unwrap();
            let x = r_point.x();
            let r = mod_n::<C>(*x);

            // Calculate `s`
            let s = k_inv * (msg_hash + (r * sk));

            // Sanity check. Ensure we construct a valid signature. So lets verify it
            {
                let s_inv = s.invert().unwrap();
                let u_1 = msg_hash * s_inv;
                let u_2 = r * s_inv;
                let r_point = ((g * u_1) + (public_key * u_2))
                    .to_affine()
                    .coordinates()
                    .unwrap();
                let x_candidate = r_point.x();
                let r_candidate = mod_n::<C>(*x_candidate);
                assert_eq!(r, r_candidate);
            }

            let aux_generator = C::CurveExt::random(OsRng).to_affine();
            let circuit = TestCircuitEcdsaVerify::<C, N> {
                public_key: Value::known(public_key),
                signature: Value::known((r, s)),
                msg_hash: Value::known(msg_hash),
                aux_generator,
                window_size: 4,
                ..Default::default()
            };

            let (rns_base, rns_scalar, _) = setup::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(0);
            let rns_base = Rc::new(rns_base);
            let rns_scalar = Rc::new(rns_scalar);

            let public_key = Point::new(Rc::clone(&rns_base), public_key);
            let mut public_data = public_key.public();

            let msg_hash = Integer::from_fe(msg_hash, Rc::clone(&rns_scalar));
            public_data.extend(msg_hash.limbs());

            let r = Integer::from_fe(r, Rc::clone(&rns_scalar));
            public_data.extend(r.limbs());

            let one = num_bigint::BigUint::one();
            let one = Integer::from_big(one, Rc::clone(&rns_scalar));
            let one_limbs = one.limbs();
            public_data.extend(one_limbs);

            // Order is: pkey, msg_hash, r, ones
            let instance = vec![public_data];
            mock_prover_verify(&circuit, instance);
        }

        use crate::curves::bn256::Fr as BnScalar;
        use crate::curves::pasta::{Fp as PastaFp, Fq as PastaFq};
        use crate::curves::secp256k1::Secp256k1Affine as Secp256k1;
        run::<Secp256k1, BnScalar>();
        // run::<Secp256k1, PastaFp>();
        // run::<Secp256k1, PastaFq>();
    }
}
