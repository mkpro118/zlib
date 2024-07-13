#![allow(clippy::missing_errors_doc, clippy::missing_panics_doc)]

use crate::zlib::adler::adler32;
use crate::zlib::bitwriter::BitWriter;
use crate::zlib::huffman::{
    get_distance_code, get_length_code, HuffmanTree, ZLIB_MAX_STRING_LENGTH,
    ZLIB_MIN_STRING_LENGTH, ZLIB_WINDOW_SIZE,
};
use crate::zlib::lz77::{LZ77Compressor, LZ77Unit};
use LZ77Unit::{Literal, Marker};

const SIXTEEN_KB: usize = 16 * 1024;

pub enum Strategy {
    Auto,
    Dynamic,
    Fixed,
    Raw,
}

#[allow(clippy::unusual_byte_groupings, clippy::cast_possible_truncation)]
#[must_use]
pub fn compress(data: &[u8], strategy: &Strategy) -> Vec<u8> {
    use Strategy::{Auto, Dynamic, Fixed, Raw};
    const COMPRESSION_METHOD: u8 = 0b0000_1000;
    const COMPRESSION_INFO: u8 = 0b0111_0000;
    const FDICT_MASK: u8 = 0b00_1_00000;
    const FLEVEL_MASK: u8 = 0b11_000000;
    const NO_FDICT_OR_FLEVEL: u8 = !(FDICT_MASK | FLEVEL_MASK);

    let mut bitwriter = BitWriter::new();

    let cmf = COMPRESSION_INFO | COMPRESSION_METHOD;
    bitwriter.write_byte(cmf);

    let fcheck = 31 - (((cmf as usize) * 256) % 31);
    assert!(
        fcheck & 0b111_00000 == 0,
        "Incorrect FCHECK, more than 5 bits!!"
    );

    // Clear the FDICT and FLEVEL bits;
    let flg = (fcheck as u8) & NO_FDICT_OR_FLEVEL;
    bitwriter.write_byte(flg);

    match strategy {
        Dynamic => compress_dynamic(&mut bitwriter, data),
        Fixed => compress_fixed(&mut bitwriter, data),
        Raw => compress_raw(&mut bitwriter, data),
        Auto => {}
    };

    // Checksum
    let checksum = adler32(data).to_be_bytes();
    bitwriter.write_bytes(&checksum);

    bitwriter.finish()
}

#[allow(clippy::cast_possible_truncation)]
fn compress_raw(writer: &mut BitWriter, data: &[u8]) {
    let n_blocks = data.len().div_ceil(SIXTEEN_KB) - 1;

    for (curr_block, chunk) in data.chunks(SIXTEEN_KB).enumerate() {
        writer.write_bit(u8::from(curr_block == n_blocks));
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

fn compress_fixed(writer: &mut BitWriter, data: &[u8]) {
    let compressor = get_zlib_compressor();
    let (mut length_tree, mut distance_tree) = HuffmanTree::get_zlib_fixed();
    length_tree.assign();
    distance_tree.assign();

    for unit in compressor.compress(data) {
        match unit {
            Literal(byte) => {
                literal_writer(&length_tree, writer, char::from(byte))
            }
            Marker(length, distance) => {
                length_writer(&length_tree, writer, length);
                distance_writer(&distance_tree, writer, distance);
            }
        }
    }

    literal_writer(&length_tree, writer, '\u{100}');
}

fn compress_dynamic(_writer: &mut BitWriter, _data: &[u8]) {
    todo!()
    // literal_writer(&ltree, writer, 256 as char);
}

fn literal_writer(ltree: &HuffmanTree, writer: &mut BitWriter, byte: char) {
    let byte = byte as char;
    let Some((code, len)) = ltree.encode(byte) else {
        panic!("No encoding found for '{}'", byte);
    };
    writer.write_bits(code, len);
}

fn length_writer(ltree: &HuffmanTree, writer: &mut BitWriter, length: usize) {
    assert!(length > 3, "Length too short!");
    assert!(length <= 258, "Length too long!");

    let length = get_length_code(length) as u32;
    let length =
        char::from_u32(length).expect("Should convert, already checked");
    let Some((code, len)) = ltree.encode(length) else {
        panic!("No encoding found for '{}'", length);
    };
    writer.write_bits(code, len);
}

fn distance_writer(
    dtree: &HuffmanTree,
    writer: &mut BitWriter,
    distance: usize,
) {
    assert!(distance > 1, "Distance too short!");
    assert!(distance < 32768, "Distance too long!");

    let distance = get_distance_code(distance) as u32;
    let distance =
        char::from_u32(distance).expect("Should convert, already checked");
    let Some((code, len)) = dtree.encode(distance) else {
        panic!("No encoding found for '{}'", distance);
    };
    writer.write_bits(code, len);
}

#[allow(dead_code)]
fn get_zlib_compressor() -> LZ77Compressor {
    let mut compressor = LZ77Compressor::with_window_size(ZLIB_WINDOW_SIZE);
    compressor.min_match_length = ZLIB_MIN_STRING_LENGTH;
    compressor.max_match_length = ZLIB_MAX_STRING_LENGTH;
    compressor
}
