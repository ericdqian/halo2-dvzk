use super::integer::IntegerChip;
use crate::halo2;
use ecc::halo2::circuit::Layouter;
use ecc::halo2::circuit::Value;
use ecc::integer::IntegerInstructions;
use ecc::integer::Range;
use ecc::maingate::RegionCtx;
use ecc::GeneralEccChip;
use halo2::arithmetic::CurveAffine;
use halo2::halo2curves::ff::PrimeField;
use halo2::plonk::Error;

pub struct KeyGenChip<
    E: CurveAffine,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
>(GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>);

impl<E: CurveAffine, N: PrimeField, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    KeyGenChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
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
    KeyGenChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn gen_public_key(
        &self,
        aux_generator: Value<E>,
        private_key: Value<<E as CurveAffine>::ScalarExt>,
        generator_point: Value<E>,
        window_size: usize,
        layouter: &mut impl Layouter<N>,
    ) -> Result<(), Error> {
        let mut ecc_chip = self.ecc_chip();

        layouter.assign_region(
            || "assign aux values",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                ecc_chip.assign_aux_generator(ctx, aux_generator)?;
                ecc_chip.assign_aux(ctx, window_size, 1)?;
                Ok(())
            },
        )?;

        let scalar_chip = ecc_chip.scalar_field_chip();
        let base_chip = ecc_chip.base_field_chip();

        let is_equal = layouter.assign_region(
            || "region 0",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let private_key = ecc_chip.new_unassigned_scalar(private_key);
                let private_key = scalar_chip.assign_integer(ctx, private_key, Range::Remainder)?;

                let generator_in_circuit = ecc_chip.assign_point(ctx, generator_point)?;
                let public_key =
                    ecc_chip.mul(ctx, &generator_in_circuit, &private_key, window_size)?;

                let public_key = ecc_chip.normalize(ctx, &public_key)?;

                let is_equal_x = base_chip.is_advice_equal_to_instance(ctx, public_key.x(), 0)?;
                println!("{:?}", is_equal_x);
                let is_equal_y =
                    base_chip.is_advice_equal_to_instance(ctx, public_key.y(), NUMBER_OF_LIMBS)?;
                println!("{:?}", is_equal_y);
                let is_equal = base_chip.mul(ctx, &is_equal_x, &is_equal_y)?;

                Ok(is_equal)
            },
        )?;

        base_chip.expose_public(
            layouter.namespace(|| "is_equal"),
            is_equal,
            NUMBER_OF_LIMBS * 2,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::KeyGenChip;
    use crate::halo2;
    use crate::maingate;
    use ecc::integer::rns::Integer;
    use ecc::integer::rns::Rns;
    use ecc::integer::NUMBER_OF_LOOKUP_LIMBS;
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
    struct KeyGenCircuitConfig {
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

    impl KeyGenCircuitConfig {
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
            KeyGenCircuitConfig {
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
    struct KeyGenCircuit<E: CurveAffine, N: PrimeField> {
        aux_generator: Value<E>,
        generator_point: Value<E>,
        private_key: Value<<E as CurveAffine>::ScalarExt>,
        window_size: usize,

        _marker: PhantomData<N>,
    }

    impl<E: CurveAffine, N: PrimeField> Circuit<N> for KeyGenCircuit<E, N> {
        type Config = KeyGenCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
            KeyGenCircuitConfig::new::<E, N>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<N>,
        ) -> Result<(), Error> {
            let ecc_chip = GeneralEccChip::<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(
                config.ecc_chip_config(),
            );

            let key_gen_chip = KeyGenChip::new(ecc_chip.clone());

            let _ = key_gen_chip.gen_public_key(
                self.aux_generator,
                self.private_key,
                self.generator_point,
                self.window_size,
                &mut layouter,
            );

            config.config_range(&mut layouter)?;

            Ok(())
        }
    }

    #[test]
    fn test_keygen_verifier() {
        fn run<C: CurveAffine, N: FromUniformBytes<64> + Ord>() {
            let generator_point = C::generator();
            let private_key = C::Scalar::random(OsRng);

            let aux_generator = C::CurveExt::random(OsRng).to_affine();
            let circuit = KeyGenCircuit::<C, N> {
                private_key: Value::known(private_key),
                generator_point: Value::known(generator_point),
                aux_generator: Value::known(aux_generator),
                window_size: 4,
                ..Default::default()
            };
            let (rns_base, rns_scalar, _) = setup::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(0);
            let rns_base = Rc::new(rns_base);
            let rns_scalar = Rc::new(rns_scalar);
            let public_key = (generator_point * private_key).to_affine();
            let public_key = Point::new(Rc::clone(&rns_base), public_key);
            let mut public_data = public_key.public();

            let one = num_bigint::BigUint::one();
            // We can use the scalar field since we're representing a 1
            let one = Integer::from_big(one, Rc::clone(&rns_scalar));
            let one_limbs = one.limbs();

            public_data.extend(one_limbs);

            let instance = vec![public_data];
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
