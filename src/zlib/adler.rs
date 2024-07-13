const ADLER_MODULO: u16 = 65521;

pub struct Adler {
    pub a: u16,
    pub b: u16,
}

impl Adler {
    pub fn from(data: &[u8]) -> Self {
        data.iter().fold(Self { a: 1, b: 0 }, |mut adler, &byte| {
            adler.a = (adler.a + (byte as u16)) % ADLER_MODULO;
            adler.b = (adler.b + adler.a) % ADLER_MODULO;
            adler
        })
    }
}
