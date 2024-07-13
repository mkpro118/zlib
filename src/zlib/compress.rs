use crate::zlib::huffman::*;
use crate::zlib::lz77::{LZ77Compressor, LZ77Unit};
use LZ77Unit::{Literal, Marker};

use super::bitwriter::BitWriter;

const SIXTEEN_KB: usize = 16 * 1024;

pub enum Strategy {
    Auto,
    Dynamic,
    Fixed,
    Raw,
}

#[must_use]
pub fn compress(data: &[u8], strategy: &Strategy) -> Vec<u8> {
    use Strategy::{Auto, Dynamic, Fixed, Raw};

    let mut bitwriter = BitWriter::new();

    const COMPRESSION_METHOD: u8 = 0b0000_1000;
    const COMPRESSION_INFO: u8 = 0b0111_0000;
    let cmf = COMPRESSION_INFO | COMPRESSION_METHOD;
    bitwriter.write_byte(cmf);

    let fcheck = 31 - (((cmf as usize) * 256) % 31);
    assert!(
        fcheck & 0b111_00000 == 0,
        "Incorrect FCHECK, more than 5 bits!!"
    );

    // Clear the FDICT and FLEVEL bits;
    const FDICT_MASK: u8 = 0b00_1_00000;
    const FLEVEL_MASK: u8 = 0b11_000000;
    const NO_FDICT_AND_FLEVEL: u8 = !(FDICT_MASK | FLEVEL_MASK);
    let flg = (fcheck as u8) & NO_FDICT_AND_FLEVEL;
    bitwriter.write_byte(flg);

    match strategy {
        Dynamic => compress_dynamic(&mut bitwriter, data),
        Fixed => compress_fixed(&mut bitwriter, data),
        Raw => compress_raw(&mut bitwriter, data),
        Auto => {}
    };

    // Checksum
    bitwriter.write_bytes(&[0].repeat(4));

    bitwriter.finish()
}

#[allow(clippy::cast_possible_truncation)]
fn compress_raw(writer: &mut BitWriter, data: &[u8]) {
    let n_blocks = data.len().div_ceil(SIXTEEN_KB) - 1;

    for (curr_block, chunk) in data.chunks(SIXTEEN_KB).enumerate() {
        writer.write_bit(if curr_block == n_blocks { 1 } else { 0 });
        writer.write_bits(0b00, 2);
        // Write length of block
        let len = data.len() as u16;
        let bytes = [(len & 0xff) as u8, (len >> 8) as u8];
        writer.write_bytes(&bytes);

        // Write one's complement of the length of block
        let len = !len;
        let bytes = [(len & 0xff) as u8, (len >> 8) as u8];
        writer.write_bytes(&bytes);

        // Write the raw block out
        writer.write_bytes(chunk);
    }
}

fn compress_fixed(_writer: &mut BitWriter, data: &[u8]) {
    let compressor = get_zlib_compressor();
    let (mut ltree, mut dtree) = HuffmanTree::get_zlib_fixed();
    ltree.assign();
    dtree.assign();

    let literal_writer = |_byte: u8| {
        todo!();
    };

    let length_writer = |_length: usize| {
        todo!();
    };

    let distance_writer = |_distance: usize| {
        todo!();
    };

    let data = compressor.compress(data);
    for unit in data {
        match unit {
            Literal(byte) => literal_writer(byte),
            Marker(length, distance) => {
                length_writer(length);
                distance_writer(distance);
            }
        }
    }
}

fn compress_dynamic(_writer: &mut BitWriter, _data: &[u8]) {
    todo!()
}

#[allow(dead_code)]
fn get_zlib_compressor() -> LZ77Compressor {
    let mut compressor = LZ77Compressor::with_window_size(ZLIB_WINDOW_SIZE);
    compressor.min_match_length = ZLIB_MIN_STRING_LENGTH;
    compressor.max_match_length = ZLIB_MAX_STRING_LENGTH;
    compressor
}
