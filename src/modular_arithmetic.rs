//! The modular arithmetic of a polynomial ring over a finite field necessary for the scheme implementation 

use ff_fft::{DensePolynomial, DenseOrSparsePolynomial};
use algebra::{Field, PrimeField, bytes::ToBytes, to_bytes};
use num::{bigint::{BigInt, Sign}, traits::{Zero, One}};
use rand::thread_rng;

/// Greastest common divisor of polynomials
pub fn gcd<F: Field>(m: &DensePolynomial<F>, n: &DensePolynomial<F>) -> DensePolynomial<F> {
    if m.is_zero() {
        if n.coeffs.iter().min() == n.coeffs.iter().max() {
            let mut res = n.clone();
            for element in res.coeffs.iter_mut() {
                *element /= &element.clone();
            }
            return res
        }
        n.clone()
    } else {
        gcd(&DenseOrSparsePolynomial::divide_with_q_and_r(&(n).into(), &(m).into()).unwrap().1, m)
    }
}

/// Extended greatest common divisor of polynomials
pub fn extended_gcd<F: PrimeField>(a: &DensePolynomial<F>, b: &DensePolynomial<F>) -> (DensePolynomial<F>, DensePolynomial<F>, DensePolynomial<F>) {
    let mut c = DensePolynomial::zero();
    if b.is_zero() {
        if a.is_zero() {
            return (DensePolynomial::zero(), DensePolynomial::zero(), DensePolynomial::zero())
        }
        c = DensePolynomial::from_coefficients_vec(vec![a.coeffs.last().unwrap().inverse().unwrap()]);
        return (&c * &a, c, DensePolynomial::zero())
    }
    else if a.is_zero() {
        c = DensePolynomial::from_coefficients_vec(vec![b.coeffs.last().unwrap().inverse().unwrap()]);
        return (&c * &b, DensePolynomial::zero(), c) 
    }
    let (mut u, mut d, mut v1, mut v3) = (DensePolynomial::from_coefficients_vec(vec!(F::one())), a.clone(), DensePolynomial::zero(), b.clone());
    let (mut q, mut r, mut old_u) = (DensePolynomial::zero(), DensePolynomial::zero(), DensePolynomial::from_coefficients_vec(vec!(F::one())));
    while !v3.is_zero() {
        q = DenseOrSparsePolynomial::divide_with_q_and_r(&(&d).into(), &(&v3).into()).unwrap().0;
        r = DenseOrSparsePolynomial::divide_with_q_and_r(&(&d).into(), &(&v3).into()).unwrap().1;
        u = v1.clone();
        d = v3.clone();
        v1 = &old_u - &(&v1 * &q);
        old_u = u.clone();
        v3 = r.clone();
    }
    let mut v = DenseOrSparsePolynomial::divide_with_q_and_r(&(&d - &(a * &u)).into(), &(b).into()).unwrap().0;
    if !d.is_zero() {
        c = DensePolynomial::from_coefficients_vec(vec![d.coeffs.last().unwrap().inverse().unwrap()]);
        d = &c * &d;
        u = &c * &u;
        v = &c * &v;       
    }
    (d, u, v)
}

/// Modular inverse of a polynomial 
pub fn modular_inverse<F: PrimeField>(x: &DensePolynomial<F>, n: &DensePolynomial<F>) -> Option<DensePolynomial<F>> {
    let one = DensePolynomial::from_coefficients_vec(vec![F::one()]);
    let (g, x, _) = extended_gcd(x, n);
    if g == one {
        let q = &DenseOrSparsePolynomial::divide_with_q_and_r(&(x).into(), &(n).into()).unwrap().1 + n;
        Some(DenseOrSparsePolynomial::divide_with_q_and_r(&(&q).into(), &(n).into()).unwrap().1)
    } else {
        None
    }
}

/// Modular exponentiation of a polynomial
pub fn modular_exponentiation<F: PrimeField>(n: &DensePolynomial<F>, e: BigInt, m: &DensePolynomial<F>) -> DensePolynomial<F> {   
    assert!(e >= Zero::zero());
    let mut result = DensePolynomial::from_coefficients_vec(vec!(F::one()));
    if e == Zero::zero() {
        return result
    }
    let mut base = DenseOrSparsePolynomial::divide_with_q_and_r(&(n).into(), &(m).into()).unwrap().1;
    let mut exp = e;
    loop {
        if &exp % 2 == One::one() {
            result = &result * &base;
            result = DenseOrSparsePolynomial::divide_with_q_and_r(&(&result).into(), &(m).into()).unwrap().1;
        }
        if exp == One::one() {
            return result
        }
        println!("exp: {}", exp);
        exp /= 2;
        base = &base * &base;
        base = DenseOrSparsePolynomial::divide_with_q_and_r(&(&base).into(), &(m).into()).unwrap().1;
    }
}

/// Checks if a polynomial is irreducible
pub fn is_irreducible<F: PrimeField>(f: &DensePolynomial<F>, q: BigInt) -> bool {
    if f.degree() == 0 {
        return false
    }
    let x = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
    let mut h = DenseOrSparsePolynomial::divide_with_q_and_r(&(&x).into(), &(f).into()).unwrap().1;
    for _k in 0..f.degree()/2 {
        h = modular_exponentiation(&h, q.clone(), &f);
        if gcd(&(&h - &x), &f) != DensePolynomial::from_coefficients_vec(vec!(F::one())) {
            return false
        }
    }
    true
}

/// Generates an irreducible polynomial
pub fn generate_irreducible<F: PrimeField>(d: usize, modulus: F) -> DensePolynomial<F> {
    let rng = &mut thread_rng();
    let mut p = DensePolynomial::zero();
    let m = BigInt::from_radix_le(Sign::Plus, &to_bytes!(modulus.into_repr_raw()).unwrap(), 256).unwrap();
    if d == 0 {
        panic!("There are no irreducible polynomials of degree zero");
    }
    else { 
        let p1 = DensePolynomial::rand(d-1, rng);
        let mut v: Vec<F> = Vec::new();
        for i in 0..d+1 {
            if i == d {
                v.push(F::one());
            }
            else {
                v.push(F::zero());
            }
        }
        let p2 = DensePolynomial::from_coefficients_vec(v);
        p = &p1 + &p2;
    }
    if is_irreducible(&p, m.clone()) {
        return p;
    } 
    else {
        generate_irreducible(d, modulus.clone())
    }
}

/// Chinese remainder theorem for polynomials 
pub fn chinese_remainder_theorem<F: PrimeField>(residues: &[DensePolynomial<F>], modulii: &[DensePolynomial<F>]) -> Option<DensePolynomial<F>> {
    let mut prod = DensePolynomial::from_coefficients_vec(vec![F::one()]);
    for i in 0..modulii.len() {
        prod = &prod * &modulii[i];
    }
    let mut sum = DensePolynomial::zero(); 
    for i in 0..residues.len() {
        let p = &prod / &modulii[i];
        sum = &sum + &(&(&residues[i] * &modular_inverse(&p, &modulii[i])?) * &p); 
    }
    Some(DenseOrSparsePolynomial::divide_with_q_and_r(&(&sum).into(), &(&prod).into()).unwrap().1)
}

#[cfg(test)]
mod tests {
    use crate::modular_arithmetic::*;
    use algebra::fields::{FpParameters, bls12_381::fr::{Fr, FrParameters}};
    use rand::thread_rng;

    #[test]
    fn gcd_test() {
        let rng = &mut thread_rng();
        let p1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "4".parse().unwrap(),
            "8".parse().unwrap(),
            "4".parse().unwrap(),
        ]);
        let p2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "2".parse().unwrap(),
            "2".parse().unwrap(),
        ]);
        let res1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "1".parse().unwrap(),
            "1".parse().unwrap(),
        ]);

        let p3 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "4".parse().unwrap(),
            "8".parse().unwrap(),
        ]);
        let p4 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "2".parse().unwrap(),
            "2".parse().unwrap(),
        ]);
        let res2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "1".parse().unwrap(),
        ]);

        let p5 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "4".parse().unwrap(),
            "4".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        let p6 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "2".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        let res3 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "2".parse().unwrap(),
            "1".parse().unwrap(),
        ]);

        assert_eq!(res1, gcd(&p1, &p2));
        assert_eq!(res2, gcd(&p3, &p4));
        assert_eq!(res3, gcd(&p5, &p6));
    }

    #[test]
    fn extended_gcd_test() {
        let p1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "4".parse().unwrap(),
            "4".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        let p2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "2".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        let res1 = (DensePolynomial::<Fr>::from_coefficients_slice(&[
            "2".parse().unwrap(),
            "1".parse().unwrap(),
        ]), DensePolynomial::<Fr>::zero(), DensePolynomial::<Fr>::from_coefficients_vec(vec![Fr::one()]));

        let p3 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "19476802767487660184210339666773165398885070582493152711402785042182663746623".parse().unwrap(),
            "39407547648466218696220377703078166300607155643001521370651489220225426932473".parse().unwrap(),
            "47052426198000984805750170658616558815668329063702121573976626273535552865243".parse().unwrap(),
        ]);
        let p4 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "50979490142702759121265333809362637261588120207351094847496358129141527548900".parse().unwrap(),
            "16843079762152759155883740107369761853538899580807489593808730337344536728087".parse().unwrap(),
            "32283086163252218186692590994158721101348092815608521201070555350148731992132".parse().unwrap(),
        ]);
        let res2 = (DensePolynomial::<Fr>::from_coefficients_vec(vec![Fr::one()]),
            DensePolynomial::<Fr>::from_coefficients_slice(&[
            "43806138258129591957903582617521875409712090892057101998166829459775902354457".parse().unwrap(),
            "11592074627960892749113633921564875200813341825841832185482104227738291318976".parse().unwrap()]),
            DensePolynomial::<Fr>::from_coefficients_slice(&[
            "44784111006087017465402644981731115561054175566352234973780986969914519054391".parse().unwrap(),
            "39964197288522477592097961220404016115972719723214298642251181946723749948019".parse().unwrap()]));

        let res3 = (DensePolynomial::<Fr>::from_coefficients_vec(vec![Fr::one()]),
            DensePolynomial::<Fr>::from_coefficients_slice(&[
            "44784111006087017465402644981731115561054175566352234973780986969914519054391".parse().unwrap(),
            "39964197288522477592097961220404016115972719723214298642251181946723749948019".parse().unwrap()]),
            DensePolynomial::<Fr>::from_coefficients_slice(&[
            "43806138258129591957903582617521875409712090892057101998166829459775902354457".parse().unwrap(),
            "11592074627960892749113633921564875200813341825841832185482104227738291318976".parse().unwrap()]));
            
        assert_eq!(res1, extended_gcd(&p1, &p2));
        assert_eq!(res2, extended_gcd(&p4, &p3));
        assert_eq!(res3, extended_gcd(&p3, &p4));
    }

    #[test]
    fn modular_inverse_test() {
        let p1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "19476802767487660184210339666773165398885070582493152711402785042182663746623".parse().unwrap(),
            "39407547648466218696220377703078166300607155643001521370651489220225426932473".parse().unwrap(),
            "47052426198000984805750170658616558815668329063702121573976626273535552865243".parse().unwrap(),
        ]);
        let p2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "50979490142702759121265333809362637261588120207351094847496358129141527548900".parse().unwrap(),
            "16843079762152759155883740107369761853538899580807489593808730337344536728087".parse().unwrap(),
            "32283086163252218186692590994158721101348092815608521201070555350148731992132".parse().unwrap(),
        ]);
        let res1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "44784111006087017465402644981731115561054175566352234973780986969914519054391".parse().unwrap(),
            "39964197288522477592097961220404016115972719723214298642251181946723749948019".parse().unwrap(),
        ]);
        let res2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "43806138258129591957903582617521875409712090892057101998166829459775902354457".parse().unwrap(),
            "11592074627960892749113633921564875200813341825841832185482104227738291318976".parse().unwrap(),
        ]); 
        assert_eq!(res1, modular_inverse(&p1, &p2).unwrap());
        assert_eq!(res2, modular_inverse(&p2, &p1).unwrap());
    }

    #[test]
    fn modular_exponentiation_test() {
        let modulus = BigInt::from_radix_le(Sign::Plus, &to_bytes!(FrParameters::MODULUS).unwrap(), 256).unwrap();

        let p1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "19476802767487660184210339666773165398885070582493152711402785042182663746623".parse().unwrap(),
            "39407547648466218696220377703078166300607155643001521370651489220225426932473".parse().unwrap(),
            "47052426198000984805750170658616558815668329063702121573976626273535552865243".parse().unwrap(),
        ]);
        let p2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "50979490142702759121265333809362637261588120207351094847496358129141527548900".parse().unwrap(),
            "16843079762152759155883740107369761853538899580807489593808730337344536728087".parse().unwrap(),
            "32283086163252218186692590994158721101348092815608521201070555350148731992132".parse().unwrap(),
        ]);
        let res1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "986003242956615429177016809436390252340141910177887281524246457542070193564".parse().unwrap(),
            "10166669723293083020254477126325769174230110203682014072807531396656242297840".parse().unwrap(),
        ]);
        let res2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "22255076073848867209901589960737345786300179849876987600668395784625859380466".parse().unwrap(),
            "12235580922986030268526276612672915531193997750620827092710604041556515391182".parse().unwrap(),
        ]);
        let p3 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "1".parse().unwrap(),
            "0".parse().unwrap(),
            "0".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        let p4 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "1".parse().unwrap(),
            "1".parse().unwrap(),
        ]);

        let exp = BigInt::parse_bytes(b"9", 10).unwrap();
        println!("exp: {}", exp);

        println!("res: {:#?}", modular_exponentiation(&p3, exp.clone(), &p4));
            
        //assert_eq!(res1, modular_exponentiation(&p1, modulus.clone(), &p2));
        //assert_eq!(res2, modular_exponentiation(&p2, modulus.clone(), &p1));
    }

    #[test]
    fn is_irreducible_test() {
        let modulus = BigInt::from_radix_le(Sign::Plus, &to_bytes!(FrParameters::MODULUS).unwrap(), 256).unwrap();

        let p1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "19476802767487660184210339666773165398885070582493152711402785042182663746623".parse().unwrap(),
            "39407547648466218696220377703078166300607155643001521370651489220225426932473".parse().unwrap(),
            "47052426198000984805750170658616558815668329063702121573976626273535552865243".parse().unwrap(),
        ]);
        let p2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "50979490142702759121265333809362637261588120207351094847496358129141527548900".parse().unwrap(),
            "16843079762152759155883740107369761853538899580807489593808730337344536728087".parse().unwrap(),
            "32283086163252218186692590994158721101348092815608521201070555350148731992132".parse().unwrap(),
        ]);
        let p3 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "52435875175126190479447740508185965837690552500527637822603658699938581184512".parse().unwrap(),
            "1".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        let p4 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "31761856654065020742413316905326188122223839894621192852980597609396047371865".parse().unwrap(),
            "42703698411488060569376726813144988309660624217638988425486872062422763151892".parse().unwrap(),
            "21374852075389287536058951024885055456920064278649108427991930654641981320396".parse().unwrap(),
        ]);

        let rng = &mut thread_rng();
        let p5 = DensePolynomial::<Fr>::rand(100, rng);

        assert_eq!(is_irreducible(&p1, modulus.clone()), false);
        //assert_eq!(is_irreducible(&p2, modulus.clone()), true);
        //assert_eq!(is_irreducible(&p3, modulus.clone()), true);
        //assert_eq!(is_irreducible(&p4, modulus.clone()), false);
        //is_irreducible(&p5, modulus.clone());
    }

    #[test]
    fn generate_irreducible_test() {
        let modulus = BigInt::from_radix_le(Sign::Plus, &to_bytes!(FrParameters::MODULUS).unwrap(), 256).unwrap();

        let p1 = generate_irreducible(2, Fr::new(FrParameters::MODULUS));
        let p2 = generate_irreducible(5, Fr::new(FrParameters::MODULUS));
    
        assert_eq!(is_irreducible(&p1, modulus.clone()), true);
        assert_eq!(is_irreducible(&p2, modulus.clone()), true);
    }

    #[test]
    fn chinese_remainder_theorem_test() {
        let p1 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "19476802767487660184210339666773165398885070582493152711402785042182663746623".parse().unwrap(),
            "39407547648466218696220377703078166300607155643001521370651489220225426932473".parse().unwrap(),
            "47052426198000984805750170658616558815668329063702121573976626273535552865243".parse().unwrap(),
        ]);
        let p2 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "50979490142702759121265333809362637261588120207351094847496358129141527548900".parse().unwrap(),
            "16843079762152759155883740107369761853538899580807489593808730337344536728087".parse().unwrap(),
            "32283086163252218186692590994158721101348092815608521201070555350148731992132".parse().unwrap(),
        ]);
        let p3 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "52435875175126190479447740508185965837690552500527637822603658699938581184512".parse().unwrap(),
            "1".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        let p4 = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "31761856654065020742413316905326188122223839894621192852980597609396047371865".parse().unwrap(),
            "42703698411488060569376726813144988309660624217638988425486872062422763151892".parse().unwrap(),
            "21374852075389287536058951024885055456920064278649108427991930654641981320396".parse().unwrap(),
        ]);

        let mut residues = Vec::new();
        let mut modulii = Vec::new();
        residues.push(p1);
        residues.push(p4);
        modulii.push(p2);
        modulii.push(p3);

        let res = DensePolynomial::<Fr>::from_coefficients_slice(&[
            "9786520344906935544568160459765845743356845108651979460168816482869661682974".parse().unwrap(),
            "10766340322107884427905321165333558738279396193962583861846953101305834763109".parse().unwrap(),
            "44827007607959443593772929055631203948344729373736301954651753168873099902448".parse().unwrap(),
            "1476819223412070859868821585185806112557670309117980133848041387704732893161".parse().unwrap(),
        ]);

        assert_eq!(res, chinese_remainder_theorem(&residues, &modulii).unwrap());
    }
}