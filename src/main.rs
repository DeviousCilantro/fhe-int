use rug::{Complete, Integer, Rational, Float};
use ring::rand::{SystemRandom, SecureRandom};
use rand::prelude::SliceRandom;
use std::io::{self, Write};
use rug::ops::Pow;

// Generate a random integer between lower and upper
fn random_integer_between(lower: &Integer, upper: &Integer) -> Integer {
    assert!(lower <= upper);
    let diff = upper.clone() - lower.clone();
    let num_bits = diff.significant_bits() as usize;
    let mut random_bytes = vec![0u8; (num_bits + 7) / 8];
    let rng = SystemRandom::new();
    loop {
        rng.fill(&mut random_bytes).unwrap();
        let random_int = Integer::from_digits(&random_bytes, rug::integer::Order::Lsf);
        if random_int <= diff {
            return lower.clone() + random_int;
        }
    }
}

// Sample integers from the given distribution to create the public key
fn sample_from_distribution(p: &Integer, lambda: u32) -> Integer {
    // Choose q from (0, 2^(lambda^2) / p)
    let q = random_integer_between(&Integer::ZERO, &(Integer::u_pow_u(2, lambda.pow(2)).complete() / p.clone()));
    // Choose r from (-2^lambda, 2^lambda)
    let r = random_integer_between(&Integer::u_pow_u(2, lambda).complete().as_neg(), &Integer::u_pow_u(2, lambda).complete());
    (p * q) + r
}

// Convert from UTF-8 string to binary
fn string_to_binary(input: &str) -> String {
    input.chars().map(|c| format!("{:08b}", c as u8)).collect()
}

// Perform the balanced modulo operation (z mod p) ∈ (-p/2, p/2]
fn balanced_modulo(p: &Integer, z: &Integer) -> Integer {
    let mut remainder = z.clone() % p.clone();
    let half_p = p.clone() >> 1;  // equivalent to p/2

    if remainder > half_p {
        remainder -= p.clone();
    }

    remainder
}

// Convert from binary to UTF-8
fn binary_to_string(input: &str) -> Result<String, std::num::ParseIntError> {
    input
        .as_bytes()
        .chunks(8)
        .map(|chunk| {
            let s = std::str::from_utf8(chunk).unwrap();
            u8::from_str_radix(s, 2).map(|byte| byte as char)
        })
    .collect()
}

// Generate the (public, private) keypair
fn generate(lambda: u32) -> (Integer, Vec<u8>, Vec<Integer>, Vec<Float>) {
    let mut sk: Integer;

    // Generate an odd integer in the given bounds
    loop {
        sk = random_integer_between(&Integer::u_pow_u(2, lambda.pow(2) - 1).complete(), &Integer::u_pow_u(2, lambda.pow(2)).complete());
        if !sk.is_divisible(&Integer::from(2)) { break; }
    }

    // Length of the pk vector is (lambda^2 + lambda)
    let mut pk: Vec<Integer> = vec![Integer::ZERO; (lambda * (lambda + 1)) as usize];

    // Set kappa as lambda^2 / 2
    let kappa = lambda.pow(2) / 2;

    // Set theta as kappa * ilog2(lambda)
    let theta = kappa * lambda.ilog2();

    // Set x_p = 2^kappa / p (rounded)
    let xp = Integer::from(2).pow(kappa).div_rem_round(sk.clone()).0;

    // Create a vector with the given number of bits with Hamming weight lambda
    let mut s = vec![1; lambda as usize]
        .into_iter()
        .chain(vec![0; (theta - lambda) as usize])
        .collect::<Vec<u8>>();

    // Shuffle the vector to randomize it
    s.shuffle(&mut rand::thread_rng());

    // Find the indices of 1s in the vector
    let positions: Vec<usize> = s
        .iter()
        .enumerate()
        .filter_map(|(i, &v)| if v == 1 { Some(i) } else { None })
        .collect();

    // Length of u vector is theta
    let mut u = vec![Integer::ZERO; theta as usize];
    let mut y: Vec<Float>;

    loop {
        // Sample integers from the given distribution and assign to public key vector
        pk
            .iter_mut()
            .for_each(|x| *x = sample_from_distribution(&sk, lambda));

        // Ensure the first element of the public key is the greatest
        if let Some(max_index) = pk.iter().enumerate().max_by_key(|(_, &ref val)| val).map(|(idx, _)| idx) {
            pk.swap(max_index, 0);
        };

        // If the first element is odd but, modulo sk, is even, then break
        if !pk[0].clone().is_divisible(&Integer::from(2)) && balanced_modulo(&sk, &pk[0]).is_divisible(&Integer::from(2)) { break; }
    }

    loop {
        // Choose random integers in the given bounds
        u
            .iter_mut()
            .for_each(|x| *x = random_integer_between(&Integer::ZERO, &Integer::from(2).pow(kappa + 1)));

        // Calculate the sum of all elements of the u vector in the indices with values equivalent to elements in
        // positions
        let sum_init = positions.iter().fold(Integer::from(0), |acc,  &index| acc + &u[index]);

        // Find the difference between x_p and sum_init modulo 2^(kappa + 1)
        let adjustment = xp.clone() - balanced_modulo(&Integer::from(2).pow(kappa + 1), &sum_init);

        // Randomly add the adjustment to an element in one of the 'positions' indices to ensure
        // the sum of the elements equals x_p
        u[*positions.choose(&mut rand::thread_rng()).unwrap()] += adjustment;

        // Recalculate the sum of the elements
        let sum = positions.iter().fold(Integer::from(0), |acc,  &index| acc + &u[index]);

        // Set y_i = u_i / 2^kappa
        y = u.iter().map(|x| {
                         let rational = Rational::from((x.clone(), Integer::from(2).pow(kappa)));
                         Float::with_val(kappa, rational)
                         }).collect();

        // Calculate the sum of the elements of the y vector in the indices with values equivalent
        // to elements in 'positions'
        let sum_y = Float::with_val(kappa, positions.iter().fold(Float::with_val(64, 0.0), |acc, &index| acc + y[index].clone()));

        // Compute sum_y modulo 2
        let sum_y_div_2: Float = sum_y.clone() / 2;
        let sum_y_mod_2  = sum_y - (sum_y_div_2.floor() * 2.0);

        // Calculate the difference between sum_y mod 2 and 1/sk
        let sk_inverse = Float::with_val(kappa, Rational::from((1, sk.clone())));
        let delta = Float::with_val(kappa, sum_y_mod_2 - sk_inverse);

        // Break if sum = x_p (mod 2^(kappa + 1)) and |sum_y mod 2 - 1/sk| < 2^(-kappa)
        if balanced_modulo(&Integer::from(2).pow(kappa + 1), &(sum.clone() - xp.clone())) == 0 && 
            delta.abs() <= Float::with_val(kappa, Rational::from((1, Integer::from(2).pow(kappa)))) { break; }

    }

    (sk, s, pk, y)

}

// Encrypt plaintext bitwise given pk and lambda (from the somewhat-HE scheme)
fn encrypt(m: &Integer, pk: &[Integer], lambda: u32) -> Integer {

    // Calculate the order of the random subset S
    let order = random_integer_between(Integer::ONE, &Integer::from(lambda * (lambda + 1)));

    // Calculate a random secondary noise parameter in the bound (-2^(2 * lambda), 2^(2 * lambda))
    let r = random_integer_between(&(Integer::ZERO - Integer::u_pow_u(2, lambda * 2).complete()), &Integer::u_pow_u(2, lambda * 2).complete());

    // Initialize the PRNG
    let mut rng = rand::thread_rng();

    // Populate the subset with random elements from pk given the order
    let s: Vec<Integer> = pk.choose_multiple(&mut rng, order.to_usize().unwrap()).cloned().collect();

    // Find the sum of the elements in the subset S
    let sum: Integer = s.iter().sum();

    // Calculate ciphertext as m + 2r + 2sum (mod pk[0])
    balanced_modulo(&pk[0], &(m + (2 * r) + (2 * sum)))
}

// Evaluate the z-vector for given ciphertext (from the bootstrappable FHE variant)
fn encrypt_evaluate(ciphertext: &Integer, y: &[Float], lambda: u32) -> Vec<Float> {
    // Set z_i = ciphertext * y_i (mod 2)
    y
        .iter()
        .map(|x| {
            // Reduce modulo 2
            let ciphertext = Float::with_val(lambda, ciphertext.clone());
            let prod = ciphertext.clone() * x.clone();
            let mut prod_div_2: Float = prod.clone() / 2;
            prod_div_2.floor_mut();
            let y = 2 * prod_div_2;
            let reduced = prod.clone() - y;
            // Keep only ilog2(lambda) + 3 bits of precision after the binary point
            let mut shifted: Float = reduced * (lambda.ilog2() + 3);
            shifted.floor_mut();
            shifted /= lambda.ilog(2) + 3;
            shifted
        })
    .collect()
}

// Decrypt ciphertext given sk (from the somewhat-HE scheme)
fn decrypt(ciphertext: &Integer, sk: &Integer) -> Integer {
    // Calculate decrypted bit = (ciphertext mod sk) (mod 2)
    balanced_modulo(sk, ciphertext).modulo(&Integer::from(2))
}

// Decrypt ciphertext given s and z (from the squashed decryption circuit of the bootstrappable FHE variant)
fn decrypt_squash(ciphertext: &Integer, s: &[u8], z: &[Float]) -> Integer {
    // Calculate the sum of s_i*z_i (each of which will produce rational numbers at the 'positions'
    // indices and 0 elsewhere)
    let sum = z.iter().zip(s.iter()).map(|(zi, &si)| zi * Float::with_val(64, si)).fold(Float::with_val(64, 0.0), |acc, x| acc + x);
    let sum = sum.round();
    let sum = sum.to_integer().unwrap();

    // Return ciphertext - sum (mod 2)
    (ciphertext - sum).modulo(&Integer::from(2))
}

// Perform sample homomorphic evaluations using bivariate polynomials (ADD, MULT gates) for testing
fn homo_evaluate(sk: &Integer, s: &[u8], pk: &[Integer], y: &[Float], pt1: &str, pt2: &str) {
    println!("Sampling x as \'{pt1}\' and y as \'{pt2}\'\n");

    // Plaintexts have to be of the same length
    assert!(pt1.len() == pt2.len());

    // Compute the encryption of pt1
    let enc1: Vec<Integer> = string_to_binary(pt1)
        .chars()
        .map(|x| encrypt(&Integer::from_str_radix(&x.to_string(), 2).unwrap(), pk, 64))
        .collect();

    // Compute the encryption of pt2
    let enc2: Vec<Integer> = string_to_binary(pt2)
        .chars()
        .map(|x| encrypt(&Integer::from_str_radix(&x.to_string(), 2).unwrap(), pk, 64))
        .collect();

    // Compute the encrypted polynomial operation (x^2 + 2xy + y^2) of enc1, enc2

    // Compute the z-vector 
    let z_x: Vec<Vec<Float>> = enc1
        .iter()
        .zip(
            enc2.iter())
        .map(|(a, b)| encrypt_evaluate(&(a.pow(2).complete() + (Integer::from(2 * a) * b) + b.pow(2).complete()), y, 64))
        .collect();

    // Compute the homomorphic encryption
    let enc_x: Vec<Integer> = enc1
        .iter()
        .zip(
            enc2.iter())
        .map(|(x, y)| (x.pow(2).complete() + (Integer::from(2 * x) * y) + y.pow(2).complete()))
        .collect();


    // Compute the encrypted polynomial operation (x + y)^2 of enc1, enc2

    // Compute the z-vector 
    let z_y: Vec<Vec<Float>> = enc1
        .iter()
        .zip(
            enc2.iter())
        .map(|(a, b)| encrypt_evaluate(&(a + b).complete().pow(2), y, 64))
        .collect();

    // Compute the homomorphic encryption
    let enc_y: Vec<Integer> = enc1
        .iter()
        .zip(
            enc2.iter())
        .map(|(x, y)| (x + y).complete().pow(2))
        .collect();

    // Compute the decryption of (enc_x, z_x) using the squashed circuit
    let dec_x: String = enc_x
        .iter()
        .enumerate()
        .map(|(i, x)| {
            let decrypted: Integer = decrypt_squash(x, s, &z_x[i]);
            assert!(decrypted == decrypt(x, sk));
            if decrypted == 0 { '0' } else { '1' }
        })
    .collect();

    // Compute the decryption of (enc_y, z_y) using the squashed circuit
    let dec_y: String = enc_y
        .iter()
        .enumerate()
        .map(|(i, x)| {
            let decrypted: Integer = decrypt_squash(x, s, &z_y[i]);
            assert!(decrypted == decrypt(x, sk));
            if decrypted == 0 { '0' } else { '1' }
        })
    .collect();

    let dec_x = Integer::from_str_radix(&dec_x, 2).unwrap();
    let dec_y = Integer::from_str_radix(&dec_y, 2).unwrap();

    // Compute the integral equivalent of the binary representation of pt1, pt2
    let pt1 = Integer::from_str_radix(&string_to_binary(pt1), 2).unwrap();
    let pt2 = Integer::from_str_radix(&string_to_binary(pt2), 2).unwrap();

    let eval = (pt1.clone() & pt1.clone()) ^ 
             (pt1.clone() & pt2.clone()) ^ 
             (pt1.clone() & pt2.clone()) ^ 
             (pt2.clone() & pt2.clone());

    println!("Evaluation on plaintexts: {eval}");
    println!("Decryption of evaluated result for (x^2 + 2xy + y^2): {dec_x}");
    println!("Decryption of evaluated result for (x + y)^2: {dec_y}");

    // Ensure correctness of homomorphic evaluation
    assert!(dec_x == eval);
    assert!(dec_y == eval);

    println!("\nHomomorphism verified.");
}

fn main() {
    print!("Enter the plaintext: ");
    io::stdout().flush().unwrap();

    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();

    let plaintext = input.trim();

    // Set lambda to 64 for testing
    let (sk, s, pk, y) = generate(64);

    println!("sk: {sk}");
    println!("\npk: {pk:?}");

    // Ensure the first element of pk is greatest
    assert!(pk[0] == pk.iter().fold(Integer::ZERO, |max, val| if val > &max { val.clone() } else { max }));

    // Compute the encryption of plaintext
    let enc: Vec<Integer> = string_to_binary(plaintext)
        .chars()
        .map(|x| encrypt(&Integer::from_str_radix(&x.to_string(), 2).unwrap(), &pk, 64))
        .collect();

    // Compute the z-vector corresponding to the encrypted ciphertext
    let z: Vec<Vec<Float>> = enc
        .iter()
        .map(|x| encrypt_evaluate(x, &y, 64))
        .collect();

    println!("\nEncrypted: {enc:?}");

    // Perform decryption using the squashed circuit and ensure the resultant bits are equivalent
    // to that produced by the somewhat-HE scheme
    let dec: String = enc
        .iter()
        .enumerate()
        .map(|(i, x)| {
            let decrypted: Integer = decrypt_squash(x, &s, &z[i]);
            assert!(decrypted == decrypt(x, &sk));
            if decrypted == 0 { '0' } else { '1' }
        })
    .collect();

    // Convert binary to UTF-8 string
    let dec = binary_to_string(&dec).unwrap();

    println!("\nDecrypted: {dec}\n");

    // Ensure correctness of encryption/decryption
    assert!(dec == plaintext);

    // Sample homomorphic evaluation with ADD/MULT gates
    homo_evaluate(&sk, &s, &pk, &y, "Homomorphic", "Encryption!");
}
