//! Implements the secret sharing scheme 

use algebra::{PrimeField, UniformRand};
use rand::thread_rng;
use crate::modular_arithmetic::{generate_irreducible, chinese_remainder_theorem};
use ff_fft::{DensePolynomial, DenseOrSparsePolynomial};
use poly_commit::{PolynomialCommitment, LabeledPolynomial, LabeledCommitment, Evaluations, QuerySet};
use std::marker::PhantomData;

/// Parameters of the secret sharing scheme
pub struct SecretSharingScheme<F: PrimeField, PC: PolynomialCommitment<F>> {
    /// Maximum number of shares that can be known without exposing the secret.
    pub threshold: usize,
    /// Weights of the parties.
    pub weights: Vec<usize>,
    /// Number of parties
    pub n: usize,
    /// Prime defining the Zp field in which computation is taking place.
    pub prime: F,
    /// The polynomial commitment scheme
    _commitment_scheme: PhantomData<PC>,
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> SecretSharingScheme<F, PC> {
    /// Creates a new secret sharing scheme
    pub fn new(threshold: usize, weights: Vec<usize>, prime: F) -> Self {
        Self {
            threshold,
            weights: weights.clone(),
            n: weights.len(),
            prime, 
            _commitment_scheme: PhantomData::<PC>,
        }
    }
    /// Each party generates his own subsecret, a polynomial of degree 0
    pub fn generate_subsecrets(&self) -> Vec<DensePolynomial<F>> {
        let rng = &mut thread_rng();
        let mut s: Vec<DensePolynomial<F>> = Vec::new();
        for i in 0..self.n {
            s.push(DensePolynomial::rand(0, rng));
        }
        s
    }
    /// Each party generates a random polynomial a(x) of degree t-2 
    pub fn generate_random_polynomials(&self) -> Vec<DensePolynomial<F>> {
        let rng = &mut thread_rng();
        let mut a: Vec<DensePolynomial<F>> = Vec::new();
        for i in 0..self.n {
            a.push(DensePolynomial::<F>::rand(self.threshold-2, rng));
        }
        a
    }
    /// Each party generates an irreducible polynomial m(x) of degree equal to his weight in the scheme
    pub fn generate_irreducible_polynomials(&self) -> Vec<DensePolynomial<F>> {
        let mut m: Vec<DensePolynomial<F>> = Vec::new();
        for i in 0..self.n {
            m.push(generate_irreducible(self.weights[i], self.prime));
        }
        m
    }
    /// Secret polynomials f(x) = s + x * a(x) of each party
    pub fn compute_secret_polynomials(&self, s: &Vec<DensePolynomial<F>>, a: &Vec<DensePolynomial<F>>) ->  Vec<DensePolynomial<F>> {
        let m0 = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
        let mut f: Vec<DensePolynomial<F>> = Vec::new();
        for i in 0..self.n {
            f.push(&s[i] + &(&a[i] * &m0));
        }
        f
    }
    /// The secret (unknown to all parties) is equal to the sum of all the subsecrets
    pub fn compute_secret(&self, s: &Vec<DensePolynomial<F>>) ->  DensePolynomial<F> {
        let mut secret: DensePolynomial<F> = DensePolynomial::zero();
        for i in 0..self.n {
            secret = &secret + &s[i];
        }
        secret
    }
    /// Compute k polynomials in f(x) = m(x) * k(x) + s(x)
    pub fn compute_k_polynomials(&self, f: &Vec<DensePolynomial<F>>, m: &Vec<DensePolynomial<F>>) -> Vec<DensePolynomial<F>> {
        let mut k = Vec::new();
        for i in 0..self.n {
            for j in 0..self.n {
                let k_share = DenseOrSparsePolynomial::divide_with_q_and_r(&(&f[i]).into(), &(&m[j]).into()).unwrap().0;
                k.push(k_share);
            }
        }
        k
    }
    /// There are n*n total subshares: s_ij(x) = f_i(x) mod m_j(x)
    /// Each party i computes and distributes n subshares of their secret polynomial (including their own)
    /// Each party j computes one secret share equal to the sum of their subshares
    pub fn compute_shares(&self, f: &Vec<DensePolynomial<F>>, m: &Vec<DensePolynomial<F>>) ->  (Vec<DensePolynomial<F>>, Vec<DensePolynomial<F>>) {
        let mut shares: Vec<DensePolynomial<F>> = vec![DensePolynomial::zero(); self.n];
        let mut subshares: Vec<DensePolynomial<F>> = Vec::new();
        for i in 0..self.n {
            for j in 0..self.n {
                let remainder = &DenseOrSparsePolynomial::divide_with_q_and_r(&(&f[i]).into(), &(&m[j]).into()).unwrap().1;
                subshares.push(remainder.clone());
            }
        }
        for i in 0..self.n {
            for j in 0..self.n {
                shares[j] = &shares[j] + &subshares[i*self.n+j];
            }
        }

        (subshares, shares)
    }
    /// Setup of the polynomial scheme
    pub fn setup(&self) -> (PC::CommitterKey, PC::VerifierKey) {
        let rng = &mut thread_rng();
        let maximum_degree = self.threshold - 1; 
        let pp = PC::setup(maximum_degree.clone(), rng).unwrap();
        let (ck, vk) = PC::trim(&pp, maximum_degree.clone(), None).unwrap();
        (ck, vk)
    } 
    /// Each party i makes and sends commitments of their polynomials f(x) and k(x)
    pub fn commit_polynomials(&self, ck: &PC::CommitterKey, f: &Vec<DensePolynomial<F>>, k: &Vec<DensePolynomial<F>>) -> 
    (Vec<LabeledPolynomial<F>>, Vec<LabeledCommitment<PC::Commitment>>, Vec<PC::Randomness>) {
        let rng = &mut thread_rng();

        let mut polynomials = Vec::new();
        for j in 0..f.len() {
            polynomials.push(LabeledPolynomial::new_owned(
                String::from("test"),
                f[j].clone(),
                None,
                None,
            ));
        }
        for j in 0..k.len() {
            polynomials.push(LabeledPolynomial::new_owned(
                String::from("test"),
                k[j].clone(),
                None,
                None,
            ));
        }
        let (comms, rands) = PC::commit(ck, &polynomials, Some(rng)).unwrap();
        (polynomials, comms, rands)
    }
    /// Each party i opens the polynomials at a given point and sends the evaluation proofs to the other parties, that can verify
    pub fn open_polynomials(&self, ck: &PC::CommitterKey, vk: &PC::VerifierKey, comms: &Vec<LabeledCommitment<PC::Commitment>>, 
        polynomials: &Vec<LabeledPolynomial<F>>, rands: &Vec<PC::Randomness>, point: F) -> (Vec<F>, Vec<F>) {
        let mut query_set = QuerySet::new();
        let mut values = Evaluations::new();
        let mut f_values = Vec::new();
        let mut k_values = Vec::new();
        let mut f_labels = Vec::new();
        let mut k_labels = Vec::new();
        let rng = &mut thread_rng();
        for i in 0..self.n {
            let label = format!("test");
            f_labels.push(label.clone());
        }
        for i in self.n..polynomials.len() {
            let label = format!("test");
            k_labels.push(label.clone());
        }
        for (i, label) in f_labels.iter().enumerate() {
            query_set.insert((label, point));
            let value = polynomials[i].evaluate(point);
            values.insert((label, point), value.clone());
            f_values.push(value.clone());
        }
        for (i, label) in k_labels.iter().enumerate() {
            query_set.insert((label, point));
            let value = polynomials[i+self.n].evaluate(point);
            values.insert((label, point), value.clone());
            k_values.push(value.clone());
        }
        let opening_challenge = UniformRand::rand(rng);
        let proof = PC::batch_open(ck, polynomials, &query_set, opening_challenge, rands).unwrap();
        let result = PC::batch_check(
            vk,
            comms,
            &query_set,
            &values,
            &proof,
            opening_challenge,
            rng,
        ).unwrap();

        assert_eq!(result, true);

        (f_values, k_values)
    }
    /// Each party j can verify that, for a given point p, f_i(p) = k_i(p)*m_j(p) + s_ij(p)
    /// And, thus, verifies that eachb subshare s_ij is valid
    pub fn verify_shares(&self, point: F, f_values: &Vec<F>, k_values: &Vec<F>, subshares: &Vec<DensePolynomial<F>>, m: &Vec<DensePolynomial<F>>) {
        let subshares_evaluations = Self::evaluate_subshares(point.clone(), subshares);
        let m_evaluations = Self::evaluate_m(point.clone(), m);

        for i in 0..self.n {
            for j in 0..self.n {
                let f_evaluation = DensePolynomial::from_coefficients_vec(vec![f_values[i]]);
                let m_evaluation = DensePolynomial::from_coefficients_vec(vec![m_evaluations[j]]);
                let s_evaluation = DensePolynomial::from_coefficients_vec(vec![subshares_evaluations[i*self.n+j]]);
                let k_evaluation = DensePolynomial::from_coefficients_vec(vec![k_values[i*self.n+j]]);
                assert_eq!(f_evaluation, &(&k_evaluation*&m_evaluation) + &s_evaluation);
            }
        }
    }
    /// Each party j evaluates the polynomials subshares at a given point: s_ij(p)
    pub fn evaluate_subshares(point: F, subshares: &Vec<DensePolynomial<F>>) -> Vec<F> {
        let mut subshares_evaluations = Vec::new();
        for i in 0..subshares.len() {
            let evaluation = subshares[i].evaluate(point);
            subshares_evaluations.push(evaluation);
        }
        subshares_evaluations
    }
    /// Each party j evaluates the polynomials m(x) at a given point: m_j(p)
    pub fn evaluate_m(point: F, m: &Vec<DensePolynomial<F>>) -> Vec<F> {
        let mut m_evaluations = Vec::new();
        for i in 0..m.len() {
            let evaluation = m[i].evaluate(point);
            m_evaluations.push(evaluation);
        }
        m_evaluations
    }
    /// Chinese remainder theorem for reconstructing (or not) the secret,
    /// equal to the coefficient of degree zero of the polynomial that is the solution for the congruence system
    pub fn reconstruct_secret(&self, shares: &[DensePolynomial<F>], m: &[DensePolynomial<F>]) -> DensePolynomial<F> {
        let m0 = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
        let crt = chinese_remainder_theorem(shares, m).unwrap();
        DenseOrSparsePolynomial::divide_with_q_and_r(&(&crt).into(), &(&m0).into()).unwrap().1
    }
}

#[cfg(test)]
mod tests {
    use crate::secret_sharing_scheme::*;
    use algebra::fields::bls12_381::fr::{Fr, FrParameters};
    use algebra::curves::models::bls12::Bls12;
    use algebra::curves::bls12_381::Bls12_381Parameters;
    use poly_commit::marlin_kzg10::MarlinKZG10;
    use algebra::fields::FpParameters;

    #[test]
    fn test() {
        let sss = SecretSharingScheme::<Fr, MarlinKZG10<Bls12<Bls12_381Parameters>>>::new(5, vec![2, 2, 3], Fr::new(FrParameters::MODULUS));
        let s = sss.generate_subsecrets();
        let secret = sss.compute_secret(&s);
        let a = sss.generate_random_polynomials();
        let m = sss.generate_irreducible_polynomials();
        let f = sss.compute_secret_polynomials(&s, &a);
        let k = sss.compute_k_polynomials(&f, &m);
        let (subshares, shares) = sss.compute_shares(&f, &m);
        let rng = &mut thread_rng();
        let point: Fr = UniformRand::rand(rng);

        let (ck, vk) = sss.setup();

        let (polynomials, comms, rands) = sss.commit_polynomials(&ck,&f, &k);

        let (f_values, k_values) = sss.open_polynomials(&ck, &vk, &comms, &polynomials, &rands, point.clone());

        sss.verify_shares(point.clone(), &f_values, &k_values, &subshares, &m);

        let res1 = sss.reconstruct_secret(&shares, &m);
        let res2 = sss.reconstruct_secret(&shares[0..=1], &m[0..=1]);
        let res3 = sss.reconstruct_secret(&shares[1..=2], &m[1..=2]);
        let res4 = sss.reconstruct_secret(&[shares[0].clone(), shares[2].clone()], &[m[0].clone(), m[2].clone()]);
        let res5 = sss.reconstruct_secret(&[shares[0].clone(), shares[1].clone()], &[m[0].clone(), m[1].clone()]);

        assert!(res1 == secret);
        assert!(res2 != secret);
        assert!(res3 == secret);
        assert!(res4 == secret);
        assert!(res5 != secret);
    }
}