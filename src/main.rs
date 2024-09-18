use bulletproofs::{BulletproofGens, PedersenGens};
use crt_vss_rs::ExtendedProofOfMod;
use merlin::Transcript;
use num_bigint::BigUint;
use num_primes::Generator;
use std::fs::OpenOptions;

fn get_prime_for_weight(n: usize) -> BigUint {
    BigUint::from_bytes_le(Generator::new_prime(n).to_bytes_le().as_slice())
}

fn test_vss(p: Vec<BigUint>, s: BigUint, m_size: usize) -> (std::time::Duration, std::time::Duration) {
    let p0: BigUint = (BigUint::from(1u64) << 252) + BigUint::from(27742317777372353535851937790883648493u128);

    // println!("Setting up generators");
    let pc_gens = PedersenGens::default();
    // TODO: Size this correctly
    let bp_gens = BulletproofGens::new(
        (m_size*(4*p.len() + 2) * 256usize).next_power_of_two(),
        p.len());

    // println!("Creating extended proof for VSS");
    use std::time::Instant;
    let prover_start = Instant::now();
    let (xproof, s_com, v_com, a_com, combined_a_mod_com, combined_vi_com, combined_vi_mod_com) = {
        let mut prover_transcript = Transcript::new(b"ExtendedProofOfModVSSExample");
            ExtendedProofOfMod::share(&pc_gens, &bp_gens, &mut prover_transcript, s.clone(), m_size, &p, p0.clone()).unwrap()
    };
    let prover_time = prover_start.elapsed();
    // println!("Extended proof created for secret sharing in {:.2?}", prover_time);

    let xproof_from_file: ExtendedProofOfMod = ExtendedProofOfMod::from_bytes(&xproof.to_bytes());

    let mut verifier_transcript = Transcript::new(b"ExtendedProofOfModVSSExample");
    let verify_start = Instant::now();
    if let Err(e) = xproof_from_file.verify_share(
        &pc_gens, &bp_gens, &mut verifier_transcript, s_com.clone(), &v_com, &a_com, &combined_a_mod_com, &combined_vi_com, &combined_vi_mod_com, &p, p0.clone()) {
        println!("Failed to verify proof: {:?}", e)
    }
    else {
        // println!("VSS Extended proof verified!");
    }
    let verify_time = verify_start.elapsed();
    // println!("Proof verified in {:.2?}", verify_start.elapsed());
    (prover_time, verify_time)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {

    let s = BigUint::from_bytes_le(&[209, 91, 84, 175, 236, 117, 121, 113, 47, 98, 118, 129, 54, 83, 102, 3, 97, 
                                                    121, 11, 189, 53, 191]);

    // let m_size = 1usize;
    for m_size in 1..4 {
        for num_parties in 1..5 {
            for party_weight in vec![16, 128] {
                let mut p = vec![];    
                for _i in 0..num_parties {
                    p.push(get_prime_for_weight(party_weight));
                }

                let (prover_time, verify_time) = test_vss(p, s.clone(), m_size);
                println!("{:?}, {:?}, {:?}, {:?}, {:?}", m_size, num_parties, party_weight, prover_time, verify_time);
            }
        }
    }
    Ok(())
}
