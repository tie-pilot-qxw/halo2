use rand_core::block::BlockRng;
use rand_core::block::BlockRngCore;
use rand_core::OsRng;
use tiny_keccak::Hasher;

// One number generator, that can be used as a deterministic Rng, outputing fixed values.
pub struct OneNg {}

impl BlockRngCore for OneNg {
    type Item = u32;
    type Results = [u32; 16];

    fn generate(&mut self, results: &mut Self::Results) {
        for elem in results.iter_mut() {
            *elem = 1;
        }
    }
}

pub fn one_rng() -> BlockRng<OneNg> {
    BlockRng::<OneNg>::new(OneNg {})
}

// Random number generator for testing

pub fn test_rng() -> OsRng {
    OsRng
}

fn keccak_hex<D: AsRef<[u8]>>(data: D) -> String {
    let mut hash = [0u8; 32];
    let mut hasher = tiny_keccak::Keccak::v256();
    hasher.update(data.as_ref());
    hasher.finalize(&mut hash);
    hex::encode(hash)
}

// Check the a test proof against a known hash
// Note that this function is only called in CI in "cargo test --all-fetaures"
pub fn assert_test_proof<D: AsRef<[u8]>>(hex: &str, data: D) {
    if cfg!(all(feature = "thread-safe-region", not(coverage))) {
        assert_eq!(keccak_hex(data), hex);
    }
}
