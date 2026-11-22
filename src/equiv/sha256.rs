//! SHA-256 (FIPS 180-4), for the keys of the tier cache. No crate in the
//! lock file provides it, and the function is short and fixed; the tests
//! check it against the standard's examples.

use std::fmt::Write as _;

const K: [u32; 64] = [
    0x428a_2f98,
    0x7137_4491,
    0xb5c0_fbcf,
    0xe9b5_dba5,
    0x3956_c25b,
    0x59f1_11f1,
    0x923f_82a4,
    0xab1c_5ed5,
    0xd807_aa98,
    0x1283_5b01,
    0x2431_85be,
    0x550c_7dc3,
    0x72be_5d74,
    0x80de_b1fe,
    0x9bdc_06a7,
    0xc19b_f174,
    0xe49b_69c1,
    0xefbe_4786,
    0x0fc1_9dc6,
    0x240c_a1cc,
    0x2de9_2c6f,
    0x4a74_84aa,
    0x5cb0_a9dc,
    0x76f9_88da,
    0x983e_5152,
    0xa831_c66d,
    0xb003_27c8,
    0xbf59_7fc7,
    0xc6e0_0bf3,
    0xd5a7_9147,
    0x06ca_6351,
    0x1429_2967,
    0x27b7_0a85,
    0x2e1b_2138,
    0x4d2c_6dfc,
    0x5338_0d13,
    0x650a_7354,
    0x766a_0abb,
    0x81c2_c92e,
    0x9272_2c85,
    0xa2bf_e8a1,
    0xa81a_664b,
    0xc24b_8b70,
    0xc76c_51a3,
    0xd192_e819,
    0xd699_0624,
    0xf40e_3585,
    0x106a_a070,
    0x19a4_c116,
    0x1e37_6c08,
    0x2748_774c,
    0x34b0_bcb5,
    0x391c_0cb3,
    0x4ed8_aa4a,
    0x5b9c_ca4f,
    0x682e_6ff3,
    0x748f_82ee,
    0x78a5_636f,
    0x84c8_7814,
    0x8cc7_0208,
    0x90be_fffa,
    0xa450_6ceb,
    0xbef9_a3f7,
    0xc671_78f2,
];

const H0: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

/// A running SHA-256 hash.
#[derive(Debug, Clone)]
pub(crate) struct Sha256 {
    state: [u32; 8],
    /// Bytes not yet compressed, always fewer than 64.
    buf: Vec<u8>,
    /// Bytes fed so far.
    len: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Self {
            state: H0,
            buf: Vec::with_capacity(64),
            len: 0,
        }
    }
}

impl Sha256 {
    pub(crate) fn update(&mut self, data: &[u8]) {
        self.len = self.len.wrapping_add(data.len() as u64);
        self.buf.extend_from_slice(data);
        let full = self.buf.len() / 64 * 64;
        for block in self.buf.get(..full).unwrap_or_default().chunks_exact(64) {
            compress(&mut self.state, block);
        }
        self.buf.drain(..full);
    }

    /// The digest, as 64 lowercase hex digits.
    pub(crate) fn hex(mut self) -> String {
        let bits = self.len.wrapping_mul(8);
        let mut pad = vec![0x80u8];
        while (self.buf.len() + pad.len()) % 64 != 56 {
            pad.push(0);
        }
        pad.extend_from_slice(&bits.to_be_bytes());
        // `update` would count the padding into the length; it is already
        // taken.
        self.buf.extend_from_slice(&pad);
        for block in self.buf.chunks_exact(64) {
            compress(&mut self.state, block);
        }
        self.state.iter().fold(String::new(), |mut s, w| {
            let _ = write!(s, "{w:08x}");
            s
        })
    }
}

/// The digest of `data`, in hex.
pub(crate) fn hex(data: &[u8]) -> String {
    let mut h = Sha256::default();
    h.update(data);
    h.hex()
}

fn compress(state: &mut [u32; 8], block: &[u8]) {
    let mut sched = [0u32; 64];
    for (i, c) in block.chunks_exact(4).enumerate().take(16) {
        if let (Some(slot), Ok(b)) = (sched.get_mut(i), <[u8; 4]>::try_from(c)) {
            *slot = u32::from_be_bytes(b);
        }
    }
    for i in 16..64 {
        let at = |k: usize| sched.get(k).copied().unwrap_or(0);
        let (w15, w2) = (at(i - 15), at(i - 2));
        let s0 = w15.rotate_right(7) ^ w15.rotate_right(18) ^ (w15 >> 3);
        let s1 = w2.rotate_right(17) ^ w2.rotate_right(19) ^ (w2 >> 10);
        let v = at(i - 16)
            .wrapping_add(s0)
            .wrapping_add(at(i - 7))
            .wrapping_add(s1);
        if let Some(slot) = sched.get_mut(i) {
            *slot = v;
        }
    }
    // The working variables a to h of the standard.
    let mut v = *state;
    for (k, wi) in K.iter().zip(sched.iter()) {
        let [x0, x1, x2, x3, x4, x5, x6, x7] = v;
        let s1 = x4.rotate_right(6) ^ x4.rotate_right(11) ^ x4.rotate_right(25);
        let ch = (x4 & x5) ^ (!x4 & x6);
        let t1 = x7
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(*k)
            .wrapping_add(*wi);
        let s0 = x0.rotate_right(2) ^ x0.rotate_right(13) ^ x0.rotate_right(22);
        let maj = (x0 & x1) ^ (x0 & x2) ^ (x1 & x2);
        let t2 = s0.wrapping_add(maj);
        v = [
            t1.wrapping_add(t2),
            x0,
            x1,
            x2,
            x3.wrapping_add(t1),
            x4,
            x5,
            x6,
        ];
    }
    for (s, x) in state.iter_mut().zip(v) {
        *s = s.wrapping_add(x);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_standard_examples() {
        assert_eq!(
            hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    #[test]
    fn feeding_in_pieces_gives_the_same_digest() {
        let data = vec![b'a'; 1_000_000];
        let mut h = Sha256::default();
        for piece in data.chunks(997) {
            h.update(piece);
        }
        assert_eq!(
            h.hex(),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
    }
}
