use super::integer::IntegerChip;
use crate::ecdsa::EcdsaChip;
use crate::halo2;
use crate::keygen::KeyGenChip;
use ecc::halo2::circuit::Layouter;
use ecc::halo2::circuit::Value;
use ecc::integer::AssignedInteger;
use ecc::integer::AssignedLimb;
use ecc::integer::IntegerInstructions;
use ecc::integer::Range;
use ecc::maingate::MainGateInstructions;
use ecc::maingate::RegionCtx;
use ecc::GeneralEccChip;
use halo2::arithmetic::CurveAffine;
use halo2::halo2curves::ff::PrimeField;
use halo2::plonk::Error;

use crate::keygen;

pub struct DesignatedVerifierChip<
    E: CurveAffine,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    ecc_chip: GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    keygen_chip: KeyGenChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ecdsa_chip: EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

impl<E: CurveAffine, N: PrimeField, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    DesignatedVerifierChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn new(ecc_chip: GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>) -> Self {
        let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());
        let keygen_chip = KeyGenChip::new(ecc_chip.clone());
        Self {
            ecc_chip: ecc_chip.clone(),
            keygen_chip,
            ecdsa_chip,
        }
    }

    pub fn ecdsa_chip(&self) -> &EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        &self.ecdsa_chip
    }

    pub fn keygen_chip(&self) -> &KeyGenChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        &self.keygen_chip
    }

    pub fn ecc_chip(&self) -> &GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        &self.ecc_chip
    }

    pub fn ecdsa_verify(
        &self,
        public_key: Value<E>,
        signature: Value<(E::Scalar, E::Scalar)>,
        msg_hash: Value<E::Scalar>,

        aux_generator: E,
        window_size: usize,
        layouter: &mut impl Layouter<N>,
    ) -> Result<
        AssignedInteger<<E as CurveAffine>::ScalarExt, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        Error,
    > {
        self.ecdsa_chip.verify(
            public_key,
            signature,
            msg_hash,
            aux_generator,
            window_size,
            layouter,
            (0 + 2),
        )
    }

    pub fn keygen_verify(
        &self,
        aux_generator: E,
        private_key: Value<<E as CurveAffine>::ScalarExt>,
        generator_point: Value<E>,
        window_size: usize,
        layouter: &mut impl Layouter<N>,
    ) -> Result<AssignedInteger<<E as CurveAffine>::Base, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, Error>
    {
        self.keygen_chip.gen_public_key(
            aux_generator,
            private_key,
            generator_point,
            window_size,
            layouter,
            0,
        )
    }

    pub fn or(
        &self,
        aux_generator: E,
        ecdsa_res: AssignedInteger<<E as CurveAffine>::ScalarExt, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        keygen_res: AssignedInteger<<E as CurveAffine>::Base, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        window_size: usize,
        layouter: &mut impl Layouter<N>,
    ) -> Result<(), Error> {
        let mut ecc_chip = self.ecc_chip();

        // layouter.assign_region(
        //     || "assign aux values",
        //     |region| {
        //         let offset = 0;
        //         let ctx = &mut RegionCtx::new(region, offset);
        //
        //         ecc_chip.assign_aux_generator(ctx, aux_generator)?;
        //         ecc_chip.assign_aux(ctx, window_size, 1)?;
        //         Ok(())
        //     },
        // )?;

        let scalar_chip = ecc_chip.scalar_field_chip();
        let base_chip = ecc_chip.base_field_chip();

        layouter.assign_region(
            || "region 0",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let ecdsa_decomposed = scalar_chip.decompose(ctx, &ecdsa_res)?;
                let keygen_decomposed = base_chip.decompose(ctx, &keygen_res)?;

                let maingate = base_chip.main_gate();

                let or_res = maingate.or(ctx, &ecdsa_decomposed[0], &keygen_decomposed[0])?;

                maingate.assert_one(ctx, &or_res)?;
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::DesignatedVerifierChip;
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
    struct DVCircuitConfig {
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

    impl DVCircuitConfig {
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
            DVCircuitConfig {
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
    struct DVCircuit<E: CurveAffine, N: PrimeField> {
        aux_generator: E,
        generator_point: Value<E>,
        dv_skey: Value<<E as CurveAffine>::ScalarExt>,
        window_size: usize,

        signer_pkey: Value<E>,
        signature: Value<(E::Scalar, E::Scalar)>,
        msg_hash: Value<E::Scalar>,

        _marker: PhantomData<N>,
    }

    impl<E: CurveAffine, N: PrimeField> Circuit<N> for DVCircuit<E, N> {
        type Config = DVCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
            DVCircuitConfig::new::<E, N>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<N>,
        ) -> Result<(), Error> {
            let ecc_chip = GeneralEccChip::<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(
                config.ecc_chip_config(),
            );

            let dv_chip = DesignatedVerifierChip::new(ecc_chip.clone());

            let ecdsa_res = dv_chip.ecdsa_verify(
                self.signer_pkey,
                self.signature,
                self.msg_hash,
                self.aux_generator,
                self.window_size,
                &mut layouter,
            )?;

            let keygen_res = dv_chip.keygen_verify(
                self.aux_generator,
                self.dv_skey,
                self.generator_point,
                self.window_size,
                &mut layouter,
            )?;

            dv_chip.or(
                self.aux_generator,
                ecdsa_res,
                keygen_res,
                self.window_size,
                &mut layouter,
            );

            config.config_range(&mut layouter)?;

            Ok(())
        }
    }
    fn mod_n<C: CurveAffine>(x: C::Base) -> C::Scalar {
        let x_big = fe_to_big(x);
        big_to_fe(x_big)
    }

    #[test]
    fn test_keygen_verifier() {
        fn run<C: CurveAffine, N: FromUniformBytes<64> + Ord>() {
            let generator_point = C::generator();
            let dv_skey = C::Scalar::random(OsRng);
            let mock_dv_skey = C::Scalar::random(OsRng);

            let aux_generator = C::CurveExt::random(OsRng).to_affine();

            let g = C::generator();

            // Generate a key pair
            let signer_skey = <C as CurveAffine>::ScalarExt::random(OsRng);
            let signer_pkey = (g * signer_skey).to_affine();

            let mock_signer_skey = <C as CurveAffine>::ScalarExt::random(OsRng);
            let mock_signer_pkey = (g * mock_signer_skey).to_affine();

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
            let s = k_inv * (msg_hash + (r * signer_skey));
            let mock_s = k_inv * (msg_hash + (r * mock_signer_skey));

            let circuit = DVCircuit::<C, N> {
                // Keygen
                dv_skey: Value::known(dv_skey),
                generator_point: Value::known(generator_point),

                // ECDSA
                signer_pkey: Value::known(signer_pkey),
                signature: Value::known((r, mock_s)),
                msg_hash: Value::known(msg_hash),

                aux_generator,
                window_size: 4,
                ..Default::default()
            };

            let (rns_base, rns_scalar, _) = setup::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(0);
            let rns_base = Rc::new(rns_base);
            let rns_scalar = Rc::new(rns_scalar);

            let mock_dv_pkey = (generator_point * dv_skey).to_affine();
            let mock_dv_pkey = Point::new(Rc::clone(&rns_base), mock_dv_pkey);
            let mut public_data = mock_dv_pkey.public();

            let signer_pkey = Point::new(Rc::clone(&rns_base), signer_pkey);
            public_data.extend(signer_pkey.public());

            let msg_hash = Integer::from_fe(msg_hash, Rc::clone(&rns_scalar));
            public_data.extend(msg_hash.limbs());

            let r = Integer::from_fe(r, Rc::clone(&rns_scalar));
            public_data.extend(r.limbs());

            let instance = vec![public_data];
            // Keygen, ECDSA
            // pkey (2), pkey (2), msg_hash (1), r (1)
            mock_prover_verify(&circuit, instance);
        }

        use crate::curves::bn256::Fr as BnScalar;
        use crate::curves::pasta::{Fp as PastaFp, Fq as PastaFq};
        use crate::curves::secp256k1::Secp256k1Affine as Secp256k1;
        run::<Secp256k1, BnScalar>();
        run::<Secp256k1, PastaFp>();
        run::<Secp256k1, PastaFq>();
    }
}
