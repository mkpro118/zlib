#![allow(dead_code)]

#[derive(Debug)]
pub struct BitWriter {
    buffer: Vec<u8>,
    byte: u8,
    numbits: usize,
}

impl BitWriter {
    pub fn new() -> Self {
        Self {
            buffer: Vec::new(),
            byte: 0,
            numbits: 0,
        }
    }

    pub fn write_bit(&mut self, bit: u8) {
        if self.numbits == 8 {
            self.flush_byte();
        }

        self.byte |= (bit & 1) << self.numbits;
        self.numbits += 1;
    }

    pub fn write_bits(&mut self, mut value: usize, mut num_bits: usize) {
        while num_bits > 0 {
            self.write_bit((value & 1) as u8);
            value >>= 1;
            num_bits -= 1;
        }
    }

    pub fn write_byte(&mut self, byte: u8) {
        // Flush any existing incomplete byte
        self.flush_byte();
        // Write the new byte
        self.buffer.push(byte);
    }

    pub fn write_bytes(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_byte(byte);
        }
    }

    fn flush_byte(&mut self) {
        if self.numbits > 0 {
            self.buffer.push(self.byte);
            self.byte = 0;
            self.numbits = 0;
        }
    }

    pub fn finish(mut self) -> Vec<u8> {
        self.flush_byte();
        self.buffer
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_bit() {
        let mut writer = BitWriter::new();
        let bits = [1, 0, 1, 1, 1, 0, 0, 1];
        for &bit in &bits {
            writer.write_bit(bit);
        }
        assert_eq!(writer.finish(), vec![0x9d]);
    }

    #[test]
    fn test_write_bits() {
        let mut writer = BitWriter::new();
        writer.write_bits(299, 9);
        assert_eq!(writer.finish(), vec![0x2b, 0x01]);
    }

    #[test]
    fn test_write_byte() {
        let mut writer = BitWriter::new();
        writer.write_byte(0x66);
        writer.write_byte(0x36);
        assert_eq!(writer.finish(), vec![0x66, 0x36]);
    }

    #[test]
    fn test_write_bytes() {
        let mut writer = BitWriter::new();
        writer.write_bytes(&[0x66, 0x36]);
        assert_eq!(writer.finish(), vec![0x66, 0x36]);
    }

    #[test]
    fn test_mixed_writes() {
        let mut writer = BitWriter::new();
        writer.write_bits(0b1010, 4);
        writer.write_byte(0xF0);
        writer.write_bit(1);
        writer.write_bits(0b101, 3);
        assert_eq!(writer.finish(), vec![0x0A, 0xF0, 0x0B]);
    }

    #[test]
    fn test_write_byte_with_existing_bits() {
        let mut writer = BitWriter::new();
        writer.write_bits(0b101, 3);
        writer.write_byte(0xF0);
        writer.write_byte(0xAA);
        assert_eq!(writer.finish(), vec![0x05, 0xF0, 0xAA]);
    }
}
