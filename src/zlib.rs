// Inspired from: https://pyokagan.name/blog/2019-10-18-zlibinflate/

#![allow(dead_code)]
#![allow(clippy::missing_errors_doc)]
#![allow(clippy::missing_panics_doc)]
#![allow(missing_docs)]

#[derive(Debug)]
struct BitReader<'a> {
    mem: &'a [u8],
    pos: usize,
    byte: u8,
    numbits: isize,
}

impl<'a> BitReader<'a> {
    pub fn new(mem: &'a [u8]) -> Self {
        Self {
            mem,
            pos: 0,
            byte: 0,
            numbits: 0,
        }
    }

    fn read_byte(&mut self) -> u8 {
        self.numbits = 0;
        let b = self.mem[self.pos];
        self.pos += 1;
        b
    }

    fn read_bit(&mut self) -> u8 {
        if self.numbits <= 0 {
            self.byte = self.read_byte();
            self.numbits = 8;
        }

        self.numbits -= 1;

        // shift bit out of byte
        let bit = self.byte & 1;
        self.byte >>= 1;

        bit
    }

    fn read_bits(&mut self, n: usize) -> usize {
        let mut out = 0usize;

        for i in 0..n {
            out |= (self.read_bit() as usize) << i;
        }

        out
    }

    fn read_bytes(&mut self, n: usize) -> usize {
        // read bytes as an integer in little-endian
        let mut out = 0usize;

        for i in 0..n {
            out |= (self.read_byte() as usize) << (8 * i);
        }

        out
    }
}

pub fn decompress(input: &[u8]) -> Result<Vec<u8>, String> {
    let mut reader = BitReader::new(input);

    // CMF is Compression Method and information Field
    let cmf = reader.read_byte();

    // CM is the Compression Method
    let cm = cmf & 0b1111;

    // We only support CM = 8, i.e compressed with DEFLATE
    if cm != 8 {
        return Err(format!("CM = {cm} is not a supported compression method"));
    }

    // CINFO is the Compression INFOrmation
    let cinfo = (cmf >> 4) & 0b1111;

    if cinfo > 7 {
        return Err(format!(
            "Invalid compression info, must be < 7, found {cinfo}"
        ));
    }

    // FLGS is the compression FLAGS
    let flags = reader.read_byte();
    let cmf_flags_checksum = ((cmf as usize) * 256 + (flags as usize)) % 31;

    if cmf_flags_checksum != 0 {
        return Err("CMF + FLAGS checksum failed!".to_owned());
    }

    let fdict = (flags >> 5) & 1;

    if fdict != 0 {
        return Err("Preset dictionaries are not supported".to_owned());
    }

    // Inflate the data
    let inflated = inflate(&mut reader);

    // We ignore the checksum
    let _adler32 = reader.read_bytes(4);

    Ok(inflated)
}

fn inflate(_reader: &mut BitReader) -> Vec<u8> {
    vec![0u8]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_bit() {
        let mut reader = BitReader::new(b"\x9d");
        let expected_bits: [u8; 8] = [1, 0, 1, 1, 1, 0, 0, 1];
        for &bit in &expected_bits {
            assert_eq!(reader.read_bit(), bit);
        }
    }

    #[test]
    fn test_read_bits() {
        let mut reader = BitReader::new(b"\x2b\x01");
        assert_eq!(reader.read_bits(9), 299);
    }

    #[test]
    fn test_read_byte() {
        let mut reader = BitReader::new(b"\x66\x36");
        assert_eq!(reader.read_bytes(2), 13926);
    }

    #[test]
    fn test_decompress_invalid_cm() {
        // Set CInfo correctly
        let initial = 0b0111_0000u8;
        for i in 0u8..8u8 {
            let input = [initial | i];
            let res = decompress(&input);
            assert!(&res.is_err());
        }

        for i in 9u8..=15u8 {
            let input = [initial | i];
            let res = decompress(&input);
            assert!(&res.is_err());
        }
    }

    #[test]
    fn test_decompress_invalid_cinfo() {
        // Set CM correctly
        let initial = 0b1000u8;
        for i in 8u8..=15u8 {
            let input = [initial | (i << 4)];
            let res = decompress(&input);
            assert!(res.is_err());
        }
    }

    #[test]
    fn test_decompress_checksum() {
        // Need data to be at least 6 bytes for adler32 checksum
        let mut input: [u8; 6] = [0; 6];

        // 0111 -> CINFO, 1110 -> CM
        input[0] = 0b0111_1000;

        let known_cm_value = (input[0] as usize) * 256;

        // Check all possible u8 values
        for mut i in u8::MIN..u8::MAX {
            // Need to set the FDICT bit to 0, yes this wastes 32 iterations
            // but its not noticeable, plus this is a test
            i &= 0b1101_1111;
            input[1] = i;
            let checksum = known_cm_value + (i as usize);
            let res = decompress(&input);

            // Ensure the checksum is not divisible by 31
            // If it is, skip that iteration
            if checksum % 31 == 0 {
                assert!(res.is_ok());
            } else {
                assert!(res.is_err());
            }
        }
    }

    #[test]
    fn test_decompress_fdict_set() {
        // Need data to be at least 6 bytes for adler32 checksum
        let mut input: [u8; 6] = [0; 6];

        // 0111 -> CINFO, 1110 -> CM
        input[0] = 0b0111_1000;

        let known_cm_value = (input[0] as usize) * 256;

        // Check all possible u8 values
        for mut i in u8::MIN..u8::MAX {
            // Need to set the FDICT bit to 1 to force an error
            i |= 0b0010_0000;
            input[1] = i;
            let checksum = known_cm_value + (i as usize);
            if checksum % 31 != 0 {
                continue;
            }

            let res = decompress(&input);
            assert!(res.is_err());
        }
    }
}
