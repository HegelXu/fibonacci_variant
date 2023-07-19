
use std::{marker::PhantomData};
use halo2_proofs::circuit::{Value, Layouter, AssignedCell, SimpleFloorPlanner};
use halo2_proofs::poly::Rotation;
use halo2_proofs::{plonk::*};
use halo2_proofs::arithmetic::Field;


struct Number<F: Field>(AssignedCell<F, F>);

#[derive(Clone, Debug, Copy)]
struct FiboConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    d: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

struct FiboChip<F: Field> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> FiboChip<F> {
    fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> FiboConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let d = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(d);
        meta.enable_equality(i);

        meta.create_gate("mul add gate", |meta| {
            let s = meta.query_selector(s);
            let a_tmp = meta.query_advice(a, Rotation::cur());
            let b_tmp = meta.query_advice(b, Rotation::cur());
            let c_tmp = meta.query_advice(c, Rotation::cur());
            let d_tmp = meta.query_advice(d, Rotation::cur());
            vec![s * (((a_tmp + c_tmp) * b_tmp) - d_tmp)]
        });

        FiboConfig {
            a, b, c, d, i, s,
        }
    }
    fn load_first_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: Value<F>,
        b: Value<F>,
        c: Value<F>,
    ) -> Result<(Number<F>, Number<F>, Number<F>, Number<F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.s.enable(&mut region, 0)?;

                let a_num = region.assign_advice(
                    || "a",
                    self.config.a,
                    0,
                    || a,
                ).map(Number)?;

                let b_num = region.assign_advice(
                    || "b",
                    self.config.b,
                    0,
                    || b,
                ).map(Number)?;

                let c_num = region.assign_advice(
                    || "b",
                    self.config.c,
                    0,
                    || c,
                ).map(Number)?;
                
                let d_tmp = (a+ c) * b;
                let d_num = region.assign_advice(
                    || "c",
                    self.config.d,
                    0,
                    || d_tmp,
                ).map(Number)?;

                Ok((a_num, b_num, c_num, d_num))
            },
        )
    }

    fn load_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: &Number<F>,
        b: &Number<F>,
        c: &Number<F>,
    ) -> Result<Number<F>, Error> {
        layouter.assign_region(
            || "row-load",
            |mut region| {
                self.config.s.enable(&mut region, 0)?;

                a.0.copy_advice(|| "a", &mut region, self.config.a, 0)?;
                b.0.copy_advice(|| "b", &mut region, self.config.b, 0)?;
                c.0.copy_advice(|| "c", &mut region, self.config.c, 0)?;
                
                let a_val = a.0.value().copied();
                let b_val = b.0.value().copied();
                let c_val = c.0.value().copied();
                let d = b_val * (a_val + c_val);

                region.assign_advice(
                    || "d",
                    self.config.d,
                    0,
                    || d,
                ).map(Number)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Number<F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(num.0.cell(), self.config.i, row)
    }
}

#[derive(Default)]
struct FiboCircuit<F> {
    a: Value<F>,
    b: Value<F>,
    c: Value<F>,
    num: usize,
}

impl<F: Field> Circuit<F> for FiboCircuit<F> {
    type Config = FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FiboChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>
    ) -> Result<(), Error> {
        let chip = FiboChip::construct(config);
        let (_, mut b, mut c, mut d) = chip.load_first_row(
            layouter.namespace(|| "first row"),
            self.a,
            self.b,
            self.c,
        )?;
        for _ in 4..self.num {
            let new_d = chip.load_row(
                layouter.namespace(|| "row-synthesize "),
                &b,
                &c,
                &d,
            )?;
            b = c;
            c = d;
            d = new_d;
        }
        chip.expose_public(layouter.namespace(|| "expose public"), d, 0)?;
        Ok(())
    }
}

fn get_fibovar_seq(a: u64, b: u64, c: u64, num: usize) -> Vec<u64> {
    let mut seq = vec![0; num];
    seq[0] = a;
    seq[1] = b;
    seq[2] = c;
    for i in 3..num {
        seq[i] = (seq[i - 1] + seq[i - 3]) * seq[i - 2];   
    }
    seq
}


fn main() {
    use halo2_proofs::{pasta::Fp, dev::MockProver};

    let num = 10;
    let seq = get_fibovar_seq(1, 2, 3, num);
    let res = Fp::from(seq[num - 1]);
    println!("{:?}", seq);

    let circuit = FiboCircuit {
        a: Value::known(Fp::from(1)),
        b: Value::known(Fp::from(2)),
        c: Value::known(Fp::from(3)),
        num,
    };

    let mut public_inputs = vec![res];

    let k = 8;

    // verify.
    println!("test the correct data");
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
    println!("done!");

    // fail!
    println!("test the wrong data 9999");
    public_inputs[0] = Fp::from(9999);
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
    println!("done!");
}

