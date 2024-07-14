const ADLER_MODULO: u32 = 65521;

#[must_use]
#[allow(clippy::module_name_repetitions)]
pub fn adler32(data: &[u8]) -> u32 {
    let (a, b) = data.iter().fold((1u32, 0u32), |(mut a, mut b), &byte| {
        a = (a + u32::from(byte)) % ADLER_MODULO;
        b = (b + a) % ADLER_MODULO;
        (a, b)
    });

    b << 16 | a
}
