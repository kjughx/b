// This uses 16-bit words, because addresses in 6502 are 16bits, so otherwise pointers would not work.
// To emulate 16-bit words using 8-bit registers, we use Y to hold the high byte and A to hold the low byte.

// As 6502 has a fixed stack at $0100-$01FF, we only have 255 bytes available. Machine code is loaded at $E000 by default, but can be reconfigured via LOAD_OFFSET=<offset> "linker flag".

// "Calling convention": first argument in Y:A, remaining args on the stack.

use core::ffi::*;
use core::mem::zeroed;
use core::ptr;
use crate::{Func, OpWithLocation, Global, Op, Compiler, Binop, ImmediateValue, Arg, AsmFunc, Loc};
use crate::nob::*;
use crate::{missingf, diagf};
use crate::crust::libc::*;
use crate::runner::mos6502::{Config, DEFAULT_LOAD_OFFSET};

// TODO: does this have to be a macro?
macro_rules! instr_enum {
    (enum $n:ident { $($instr:ident),* }) => {
        #[derive(Clone, Copy)]
        #[repr(u8)]
        pub enum $n {
            $($instr),*,
            COUNT
        }

        // TODO: maybe not search linearly, if this is too slow
        pub unsafe fn instr_from_string(s: *const c_char) -> Option<Instr> {
            $(
                let curr = c!(stringify!($instr));
                if (strcmp(s, curr) == 0) {
                    return Some($n::$instr);
                }
            )*
            return None;
        }
        pub unsafe fn instr_to_string(ins: Instr) -> *const c_char {
            $(
                if matches!(ins, $n::$instr) {
                    return c!(stringify!($instr));
                }
            )*
            unreachable!();
        }
    }
}

instr_enum! {
    enum Instr {
        ADC,
        AND,
        ASL,
        BCC, BCS, BEQ, BIT,
        BMI,
        BNE, BPL, BRK, BVC,
        VBS,
        CLC, CLD, CLI, CLV,
        CMP, CPX, CPY,
        DEC, DEX, DEY,
        EOR,
        INC, INX, INY,
        JMP, JSR,
        LDA, LDX, LDY,
        LSR,
        NOP,
        ORA,
        PHA, PHP, PLA, PLP,
        ROL, ROR,
        RTI, RTS,
        SBC,
        SEC, SED, SEI,
        STA, STX, STY,
        TAX, TAY, TSX, TXA, TXS, TYA
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AddrMode {
    IMM = 0,
    ZP,
    ZP_X,
    ZP_Y,
    ABS,
    ABS_X,
    ABS_Y,
    IND_X,
    IND_Y,

    ACC,
    REL,
    IND,
    IMPL, // implied, no arg

    COUNT
}
unsafe fn arg8_to_string(mode: AddrMode, v: u8) -> *const c_char {
    use AddrMode::*;
    match mode {
        IMPL => c!(""),
        IMM => temp_sprintf(c!("#0x%02x"), v as c_uint),
        ZP | ZP_X | ZP_Y | REL => temp_sprintf(c!("$0x%02x"), v as c_uint),
        IND_X => temp_sprintf(c!("($0x%02x,x)"), v as c_uint),
        IND_Y => temp_sprintf(c!("(0x%02x),y"), v as c_uint),
        _ => unreachable!(),
    }
}

unsafe fn arg16_to_string(mode: AddrMode, v: u16) -> *const c_char {
    use AddrMode::*;
    match mode {
        IMPL => c!(""),
        IMM => temp_sprintf(c!("#0x%04x"), v as c_uint),
        ABS => temp_sprintf(c!("$0x%04x"), v as c_uint),
        ABS_X => temp_sprintf(c!("$0x%04x,x"), v as c_uint),
        ABS_Y => temp_sprintf(c!("$0x%04x,y"), v as c_uint),
        IND => temp_sprintf(c!("($0x%04x)"), v as c_uint),
        _ => unreachable!(),
    }
}


use Instr::*;
use AddrMode::*;

// TODO: we currently use 0xFF for invalid opcode, because Some() and None
// make this table way too big/hard to read
const INVL: u8 = 0xFF;
const OPCODES: [[u8; AddrMode::COUNT as usize]; Instr::COUNT as usize] =
       [// IMM    ZP    ZP_X   ZP_Y,  ABS   ABS_X  ABS_Y  IND_X  IND_Y   ACC    REL   IND, IMPL
/*ADC*/[  0x69,  0x65,  0x75,  INVL, 0x6D,  0x7D,  0x79,  0x61,  0x71,  INVL,  INVL, INVL, INVL],
/*AND*/[  0x29,  0x25,  0x35,  INVL, 0x2D,  0x3D,  0x39,  0x21,  0x31,  INVL,  INVL, INVL, INVL],
/*ASL*/[  INVL,  0x06,  0x16,  INVL, 0x0E,  0x1E,  INVL,  INVL,  INVL,  0x0A,  INVL, INVL, INVL],
/*BCC*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  0x90, INVL, INVL],
/*BCS*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  0xB0, INVL, INVL],
/*BEQ*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  0xF0, INVL, INVL],
/*BIT*/[  INVL,  0x24,  INVL,  INVL, 0x2C,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*BMI*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  0x30, INVL, INVL],
/*BNE*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  0xD0, INVL, INVL],
/*BPL*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  0x10, INVL, INVL],
/*BRK*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x00],
/*BVC*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  0x50, INVL, INVL],
/*BVS*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  0x70, INVL, INVL],
/*CLC*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x18],
/*CLD*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xD8],
/*CLI*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x58],
/*CLV*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xB8],
/*CMP*/[  0xC9,  0xC5,  0xD5,  INVL, 0xCD,  0xDD,  0xD9,  0xC1,  0xD1,  INVL,  INVL, INVL, INVL],
/*CPX*/[  0xE0,  0xE4,  INVL,  INVL, 0xEC,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*CPY*/[  0xC0,  0xC4,  INVL,  INVL, 0xCC,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*DEC*/[  INVL,  0xC6,  0xD6,  INVL, 0xCE,  0xDE,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*DEX*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xCA],
/*DEY*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x88],
/*EOR*/[  0x49,  0x45,  0x55,  INVL, 0x4D,  0x5D,  0x59,  0x41,  0x51,  INVL,  INVL, INVL, INVL],
/*INC*/[  INVL,  0xE6,  0xF6,  INVL, 0xEE,  0xFE,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*INX*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xE8],
/*INY*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xC8],
/*JMP*/[  INVL,  INVL,  INVL,  INVL, 0x4C,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, 0x6C, INVL],
/*JSR*/[  INVL,  INVL,  INVL,  INVL, 0x20,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*LDA*/[  0xA9,  0xA5,  0xB5,  INVL, 0xAD,  0xBD,  0xB9,  0xA1,  0xB1,  INVL,  INVL, INVL, INVL],
/*LDX*/[  0xA2,  0xA6,  INVL,  0xB6, 0xAE,  INVL,  0xBE,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*LDY*/[  0xA0,  0xA4,  0xB4,  INVL, 0xAC,  0xBC,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*LSR*/[  INVL,  0x46,  0x56,  INVL, 0x4E,  0x5E,  INVL,  INVL,  INVL,  0x4A,  INVL, INVL, INVL],
/*NOP*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xEA],
/*ORA*/[  0x09,  0x05,  0x15,  INVL, 0x0D,  0x1D,  0x19,  0x01,  0x11,  INVL,  INVL, INVL, INVL],
/*PHA*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x48],
/*PHP*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x08],
/*PLA*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x68],
/*PLP*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x28],
/*ROL*/[  INVL,  0x26,  0x36,  INVL, 0x2E,  0x3E,  INVL,  INVL,  INVL,  0x2A,  INVL, INVL, INVL],
/*ROR*/[  INVL,  0x66,  0x76,  INVL, 0x6E,  0x7E,  INVL,  INVL,  INVL,  0x6A,  INVL, INVL, INVL],
/*RTI*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x40],
/*RTS*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x60],
/*SBC*/[  0xE9,  0xE5,  0xF5,  INVL, 0xED,  0xFD,  0xF9,  0xE1,  0xF1,  INVL,  INVL, INVL, INVL],
/*SEC*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x38],
/*SED*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xF8],
/*SEI*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x78],
/*STA*/[  INVL,  0x85,  0x95,  INVL, 0x8D,  0x9D,  0x99,  0x81,  0x91,  INVL,  INVL, INVL, INVL],
/*STX*/[  INVL,  0x86,  INVL,  0x96, 0x8E,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*STY*/[  INVL,  0x84,  0x94,  INVL, 0x8C,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, INVL],
/*TAX*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xAA],
/*TAY*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xA8],
/*TSX*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0xBA],
/*TXA*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x8A],
/*TXS*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x9A],
/*TYA*/[  INVL,  INVL,  INVL,  INVL, INVL,  INVL,  INVL,  INVL,  INVL,  INVL,  INVL, INVL, 0x98],
       ]// IMM    ZP    ZP_X   ZP_Y,  ABS   ABS_X  ABS_Y  IND_X  IND_Y   ACC    REL   IND, IMPL
    ;

// zero page addresses
// TODO: Do we really have to use
// zero page for indirect function calls
// or derefs?
const ZP_DEREF_0:       u8 = 0;
const ZP_DEREF_1:       u8 = 1;
const ZP_DEREF_STORE_0: u8 = 2;
const ZP_DEREF_STORE_1: u8 = 3;
const ZP_RHS_L:         u8 = 4;
const ZP_RHS_H:         u8 = 5;
const ZP_TMP_0:         u8 = 6;
const ZP_TMP_1:         u8 = 7;
const ZP_TMP_2:         u8 = 8;
const ZP_TMP_3:         u8 = 9;
const ZP_DEREF_FUN_0:   u8 = 10; // can't be the same as ZP_DEREF,
const ZP_DEREF_FUN_1:   u8 = 11; // as we use this before argument loading

const STACK_PAGE: u16 = 0x0100;

#[derive(Clone, Copy)]
pub enum RelocationKind {
    AddressAbs {
        idx: usize
    }, // address from Assembler.addresses
    AddressRel {
        idx: usize,
    }, // address from Assembler.addresses
    DataOffset {
        off: u16,
        low: bool
    },
    Function {
        name: *const c_char
    },
    External {
        name: *const c_char,
        byte: u8, // Indicates which address bytes to use for the relocation
                  // 0 => First byte
                  // 1 => Second byte
                  // 2 => Use both bytes
    },
    Label {
        func_name: *const c_char,
        label: usize
    },
}
impl RelocationKind {
    pub fn is16(self) -> bool {
        match self {
            RelocationKind::DataOffset{..} => false,
            RelocationKind::Function{..}   => true,
            RelocationKind::External{byte, ..} => {
                match byte {
                    0|1 => false,
                    2 => true,
                    _ => unreachable!(),
                }
            },
            RelocationKind::Label{..}      => true,
            RelocationKind::AddressRel{..} => false,
            RelocationKind::AddressAbs{..} => true,
        }
    }
}

#[derive(Clone, Copy)]
pub struct Relocation {
    pub kind: RelocationKind,
    pub addr: u16,
}

#[derive(Clone, Copy)]
pub struct Function {
    pub name: *const c_char,
    pub addr: u16,
}

#[derive(Clone, Copy)]
pub struct Label {
    pub func_name: *const c_char,
    pub label: usize,
    pub addr: u16,
}

#[derive(Clone, Copy)]
pub struct External {
    pub name: *const c_char,
    pub addr: u16,
}

#[derive(Clone, Copy)]
pub struct Assembler {
    pub relocs: Array<Relocation>,
    pub functions: Array<Function>,
    pub op_labels: Array<Label>,
    pub externals: Array<External>,
    pub addresses: Array<u16>,
    pub code_start: u16, // load address of code section
    pub frame_sz: u8, // current stack frame size in bytes, because 6502 has no base register
    pub output: *mut String_Builder,
    pub assembly: String_Builder,
}

pub unsafe fn write_byte(out: *mut String_Builder, byte: u8) {
    da_append(out, byte as c_char);
}
pub unsafe fn write_word(out: *mut String_Builder, word: u16) {
    write_byte(out, word as u8);
    write_byte(out, (word >> 8) as u8);
}
pub unsafe fn write_byte_at(out: *mut String_Builder, byte: u8, addr: u16) {
    *((*out).items.add(addr as usize)) = byte as c_char;
}
pub unsafe fn write_word_at(out: *mut String_Builder, word: u16, addr: u16) {
    write_byte_at(out, word as u8, addr);
    write_byte_at(out, (word>>8) as u8, addr+1);
}

pub unsafe fn instr0(asm: *mut Assembler, inst: Instr, mode: AddrMode) {
    let opcode = OPCODES[inst as usize][mode as usize];
    if opcode == INVL {
        printf(c!("Invalid combination of opcode and operand %u and %u\n"),
               inst as usize, mode as usize);
        abort();
    }
    write_byte((*asm).output, opcode);
}
// IMPL (implied) addressing mode
pub unsafe fn instr(asm: *mut Assembler, inst: Instr) {
    instr0(asm, inst, IMPL);
    sb_appendf(&mut (*asm).assembly, c!("  %s\n"), instr_to_string(inst));
}
pub unsafe fn instr_label(asm: *mut Assembler, inst: Instr, mode: AddrMode, label: usize) {
    instr0(asm, inst, mode);
    let kind = match mode {
        AddrMode::REL => RelocationKind::AddressRel{idx: label},
        AddrMode::ABS => RelocationKind::AddressAbs{idx: label},
        _ => unreachable!(),
    };
    add_reloc(asm, kind);
    sb_appendf(&mut (*asm).assembly, c!("  %s label_%zu\n"), instr_to_string(inst), label);
}
pub unsafe fn instr8(asm: *mut Assembler, inst: Instr, mode: AddrMode, v: u8) {
    instr0(asm, inst, mode);
    write_byte((*asm).output, v);
    sb_appendf(&mut (*asm).assembly, c!("  %s %s\n"), instr_to_string(inst), arg8_to_string(mode, v));
}
pub unsafe fn instr16(asm: *mut Assembler, inst: Instr, mode: AddrMode, v: u16) {
    instr0(asm, inst, mode);
    write_word((*asm).output, v);
    sb_appendf(&mut (*asm).assembly, c!("  %s %s\n"), instr_to_string(inst), arg16_to_string(mode, v));
}

pub unsafe fn add_reloc(asm: *mut Assembler, kind: RelocationKind) {
    let out = (*asm).output;
    da_append(&mut (*asm).relocs, Relocation {
        kind,
        addr: (*out).count as u16
    });
    if kind.is16() {
        write_word(out, 0);
    } else {
        write_byte(out, 0);
    }
}

pub unsafe fn create_address_label(asm: *mut Assembler) -> usize {
    let idx = (*asm).addresses.count;
    da_append(&mut (*asm).addresses, 0);
    idx
}
pub unsafe fn create_address_label_here(asm: *mut Assembler) -> usize {
    let label = create_address_label(asm);
    link_address_label_here(asm, label);
    label
}

// TODO: inform the caller, that `addr' is relative to code_start
pub unsafe fn link_address_label(label: usize, addr: u16, asm: *mut Assembler) {
    *(*asm).addresses.items.add(label) = addr;
}
pub unsafe fn link_address_label_here(asm: *mut Assembler, label: usize) {
    *(*asm).addresses.items.add(label) = (*((*asm).output)).count as u16;
    sb_appendf(&mut (*asm).assembly, c!("label_%zu:\n"), label);
}

pub unsafe fn load_auto_var(asm: *mut Assembler, index: usize) {
    // save current stack pointer
    instr(asm, TSX);
    // load low byte
    instr16(asm, LDA, ABS_X, STACK_PAGE + (*asm).frame_sz as u16 - (index-1) as u16 * 2 - 1);
    // load high byte
    instr16(asm, LDY, ABS_X, STACK_PAGE + (*asm).frame_sz as u16 - (index-1) as u16 * 2);
}

pub unsafe fn load_arg(asm: *mut Assembler, arg: Arg, loc: Loc) {
    match arg {
        Arg::Deref(index) => {
            load_auto_var(asm, index);

            // load address to buffer in ZP to dereference, because registers
            // only 8 bits
            instr8(asm, STA, ZP, ZP_DEREF_0);
            instr8(asm, STY, ZP, ZP_DEREF_1);

            // Y = ((0),1)
            instr8(asm, LDY, IMM, 1);
            instr8(asm, LDA, IND_Y, ZP_DEREF_0);
            instr(asm, TAY);

            // A = ((0,0))
            instr8(asm, LDX, IMM, 0);
            instr8(asm, LDA, IND_X, ZP_DEREF_0);
        },
        Arg::RefAutoVar(index)  => {
            let auto_var_address = STACK_PAGE + (*asm).frame_sz as u16 - (index-1) as u16 * 2 - 1;

            // save current stack pointer
            instr(asm, TSX);

            // load address low byte
            instr(asm, TXA);

            instr(asm, CLC);
            instr8(asm, ADC, IMM, (auto_var_address & 0xFF) as u8);

            instr8(asm, STA, ZP, ZP_TMP_0);
            instr8(asm, LDA, IMM, 0);
            instr8(asm, ADC, IMM, (auto_var_address >> 8) as u8);

            instr(asm, TAY);
            instr8(asm, LDA, ZP, ZP_TMP_0);
        }
        Arg::RefExternal(name)  => {
            // TODO: Understand why the test ref does not give the correct value to y
            // where it should write 420 to it
            // Output:
            //     y: 410 410 410 410 410

            // load address low byte
            instr8(asm, LDA, IMM, 0);

            instr(asm, CLC);
            instr0(asm, ADC, IMM);
            add_reloc(asm, RelocationKind::External{name, byte:0});

            instr8(asm, STA, ZP, ZP_TMP_0);

            instr8(asm, LDA, IMM, 0);
            instr0(asm, ADC, IMM);
            add_reloc(asm, RelocationKind::External{name, byte:1});

            instr(asm, TAY);
            instr8(asm, LDA, ZP, ZP_TMP_0);
        },
        Arg::External(name)     => {
            instr8(asm, LDX, IMM, 0);

            instr0(asm, LDA, ABS_X);
            add_reloc(asm, RelocationKind::External{name, byte: 2});

            instr8(asm, LDX, IMM, 1);
            // load high byte
            instr0(asm, LDY, ABS_X);
            add_reloc(asm, RelocationKind::External{name, byte: 2});
        },
        Arg::AutoVar(index)     => {
            load_auto_var(asm, index);
        },
        Arg::Literal(value) => {
            if value >= 65536 {
                diagf!(loc, c!("WARNING: contant $%X out of range for 16 bits\n"), value);
            }
            instr8(asm, LDA, IMM, value as u8);
            instr8(asm, LDY, IMM, (value >> 8) as u8);
        },
        Arg::DataOffset(offset) => {
            assert!(offset < 65536, "data offset out of range");
            instr0(asm, LDA, IMM);
            add_reloc(asm, RelocationKind::DataOffset{off: offset as u16, low: true});
            instr0(asm, LDY, IMM);
            add_reloc(asm, RelocationKind::DataOffset{off: (offset + 1) as u16, low: false});
        },
        Arg::Bogus => unreachable!("bogus-amogus"),
    };
}

pub unsafe fn store_auto(asm: *mut Assembler, index: usize) {
    // save current stack pointer
    instr(asm, TSX);
    // save low byte
    instr16(asm, STA, ABS_X, STACK_PAGE + (*asm).frame_sz as u16 - (index-1) as u16 * 2 - 1);

    // save high byte
    instr(asm, TYA);
    instr16(asm, STA, ABS_X, STACK_PAGE + (*asm).frame_sz as u16 - (index-1) as u16 * 2);
}

// TODO: can this be done better?
pub unsafe fn add_sp(asm: *mut Assembler, bytes: u8) {
    (*asm).frame_sz -= bytes;
    if bytes < 8 {
        for _ in 0 .. bytes {
            instr(asm, PLA);
        }
    } else {
        instr(asm, TSX);
        instr(asm, TXA);
        instr(asm, CLC);
        instr8(asm, ADC, IMM, bytes);
        instr(asm, TAX);
        instr(asm, TXS);
    }
}
// cannot modify Y:A here, as they hold first argument
// TODO: look, if this can be done without a loop, like in `add_sp` without modifying
// Y:A. Either save them temporarily or write the first arg to stack before decrementing
// SP
pub unsafe fn sub_sp(asm: *mut Assembler, bytes: u8) {
    (*asm).frame_sz += bytes;
    for _ in 0 .. bytes {
        instr(asm, PHA);
    }
}
pub unsafe fn push16(asm: *mut Assembler) {
    (*asm).frame_sz += 2;

    instr(asm, TAX);
    instr(asm, TYA);
    // push high byte first
    instr(asm, PHA);
    instr(asm, TXA);
    // then low
    instr(asm, PHA);
}
pub unsafe fn pop16_discard(asm: *mut Assembler) {
    (*asm).frame_sz -= 2;

    instr(asm, PLA);
    instr(asm, PLA);
}

// load lhs in Y:A, rhs in RHS_L:RHS_H
pub unsafe fn load_two_args(asm: *mut Assembler, lhs: Arg, rhs: Arg, op: OpWithLocation) {
    load_arg(asm, rhs, op.loc);
    instr8(asm, STA, ZP, ZP_RHS_L);
    instr8(asm, STY, ZP, ZP_RHS_H);
    load_arg(asm, lhs, op.loc);
}

// TODO: maybe recover from errors?
pub unsafe fn parse_num(line_begin: *const c_char, mut line: *const c_char, mut loc: Loc) -> (u16, *const c_char) {
    while isspace(*line as i32) != 0 {line = line.add(1);}
    let (v, mut end) = match *line as u8 {
        b'$' => {
            let mut end = ptr::null_mut();
            let v = strtoull(line.add(1), &mut end, 16);
            (v, end)
        }
        b'0'..=b'9' => {
            let mut end = ptr::null_mut();
            let v = strtoull(line, &mut end, 10);
            (v, end)
        },
        c => {
            loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
            diagf!(loc, c!("ERROR: unexpected character `%c` in __asm__ number literal\n"),
                   c as c_int);
            abort();
        }
    };
    if v > 0xFFFF {
        loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
        diagf!(loc, c!("ERROR: contant $%X out of range for 16 bits\n"), v);
        abort();
    }
    while isspace(*end as i32) != 0 {end = end.add(1);}
    (v as u16, end)
}

pub unsafe fn assemble_statement(out: *mut String_Builder,
                                 mut line: *const c_char, mut loc: Loc) {

    let line_begin = line;
    // TODO: IMPORTANT! What we are doing in here is basically lexing.
    // Consider maybe reusing and adapting our B lexer in here?
    while isspace(*line as i32) != 0 {
        line = line.add(1);
    }

    // all instruction mnemonics are 3 characters.
    let mut buf = [0i8; 4];
    for i in 0 .. 3 {
        buf[i] = toupper(*line as i32) as i8;
        if *line == 0 {
            break;
        }
        line = line.add(1);
    }

    let instr = match instr_from_string(buf.as_ptr()) {
        Some(v) => v,
        None => {
            loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
            diagf!(loc, c!("ERROR: invalid instruction mnemonic `%s`\n"), buf.as_ptr());
            abort();
        }
    };

    while isspace(*line as i32) != 0 {line = line.add(1);}

    let operand = line;
    let mut arg8 = None;
    let mut arg16 = None;
    let mut mode = match *line as u8 {
        0    => IMPL,
        b'#' => {
            line = line.add(1);

            let num;
            (num, line) = parse_num(line_begin, line, loc);
            if num > 0xFF {
                loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
                diagf!(loc, c!("ERROR: constant $%X out of range for 8 bit immediate\n"),
                       num as c_uint);
                abort();
            }
            arg8 = Some(num as u8);
            IMM
        },
        b'0'..=b'9' | b'$' => {
            let num;
            (num, line) = parse_num(line_begin, line, loc);

            arg16 = Some(num);
            if *line as u8 == b',' {
                line = line.add(1);
                while isspace(*line as i32) != 0 {line = line.add(1);}

                if toupper(*line as i32) as u8 == b'X' {
                    line = line.add(1);
                    ABS_X
                } else if toupper(*line as i32) as u8 == b'Y' {
                    line = line.add(1);
                    ABS_Y
                } else {
                    ABS
                }
            } else {
                ABS
            }
        },
        b'(' => {
            line = line.add(1);
            let num;
            (num, line) = parse_num(line_begin, line, loc);

            if *line as u8 == b',' {
                if num > 0xFF {
                    loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
                    diagf!(loc, c!("ERROR: constant $%X out of 8-bit range for indirect X\n"),
                           num as c_uint);
                    abort();
                }
                arg8 = Some(num as u8);

                line = line.add(1);
                while isspace(*line as i32) != 0 {line = line.add(1);}
                if toupper(*line as i32) as u8 != b'X' {
                    loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
                    diagf!(loc, c!("ERROR: X expected for indirect addressing mode __asm__\n"), *line as c_int);
                    abort();
                }
                line = line.add(1);
                while isspace(*line as i32) != 0 {line = line.add(1);}
                if toupper(*line as i32) as u8 != b')' {
                    loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
                    diagf!(loc, c!("ERROR: ) expected in __asm__\n"), *line as c_int);
                    abort();
                }
                line = line.add(1);
                IND_X
            } else {
                if *line as u8 != b')' {
                    loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
                    diagf!(loc, c!("ERROR: expected ',' or ')' after indirect address __asm__\n"), *line as c_int);
                    abort();
                }
                line = line.add(1);
                while isspace(*line as i32) != 0 {line = line.add(1);}

                if *line as u8 == b',' {
                    if num > 0xFF {
                        loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
                        diagf!(loc, c!("ERROR: constant $%X out of 8-bit range for indirect Y\n"),
                               num as c_uint);
                        abort();
                    }
                    arg8 = Some(num as u8);

                    line = line.add(1);
                    while isspace(*line as i32) != 0 {line = line.add(1);}
                    if toupper(*line as i32) as u8 != b'Y' {
                        loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
                        diagf!(loc, c!("ERROR: Y expected for indirect addressing mode __asm__\n"), *line as c_int);
                        abort();
                    }
                    line = line.add(1);
                    IND_Y
                } else {
                    arg16 = Some(num);
                    IND
                }
            }
        },
        c => {
            loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
            diagf!(loc, c!("ERROR: unexpected character `%c`\n"), c as c_int);
            abort();
        }
    };

    // prefer zeropage instructions, if they exist
    if let Some(v) = arg16 {
        if mode == ABS && v <= 0xFF && OPCODES[instr as usize][ZP as usize] != INVL {
            mode = ZP;
            arg8 = Some(v as u8);
            arg16 = None;
        } else if mode == ABS_X && v <= 0xFF && OPCODES[instr as usize][ZP_X as usize] != INVL {
            mode = ZP_X;
            arg8 = Some(v as u8);
            arg16 = None;
        } else if mode == ABS_Y && v <= 0xFF && OPCODES[instr as usize][ZP_Y as usize] != INVL {
            mode = ZP_Y;
            arg8 = Some(v as u8);
            arg16 = None;
        }
    }

    let opcode = OPCODES[instr as usize][mode as usize];
    if opcode == INVL {
        loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
        diagf!(loc, c!("ERROR: invalid combination of instruction `%s` and operand `%s`\n"),
               buf.as_ptr(), operand);
        abort();
    }

    write_byte(out, opcode);
    if let Some(a) = arg8 {
        write_byte(out, a);
    } else if let Some(a) = arg16 {
        write_word(out, a);
    }

    if *line != 0 {
        loc.line_offset += (line as isize - line_begin as isize + 1) as i32;
        diagf!(loc, c!("ERROR: trailing garbage: `%s`\n"), line);
        abort();
    }
}

pub unsafe fn generate_function(asm: *mut Assembler, name: *const c_char, params_count: usize, auto_vars_count: usize,
                                body: *const [OpWithLocation]) {
    let out = (*asm).output;
    (*asm).frame_sz = 0;
    let fun_addr = (*out).count as u16;
    da_append(&mut (*asm).functions, Function {
        name,
        addr: fun_addr,
    });

    // prepare function labels for each op and the end of the function
    let mut op_addresses: Array<usize> = zeroed();
    for _ in 0..=body.len() {
        let idx = (*asm).addresses.count;
        da_append(&mut op_addresses, idx);

        da_append(&mut (*asm).addresses, 0);
    }

    // TODO: use params_count, auto_vars_count
    assert!(auto_vars_count*2 < 256);
    let stack_size = (auto_vars_count * 2) as u8;
    sub_sp(asm, stack_size);

    for i in 0..(params_count as u16) {
        instr(asm, TSX);
        if i == 0 {
            // low
            instr16(asm, STA, ABS_X, STACK_PAGE + stack_size as u16 - 2*i - 1);

            // high
            instr(asm, TYA);
            instr16(asm, STA, ABS_X, STACK_PAGE + stack_size as u16 - 2*i);
            continue;
        }

        // low
        instr16(asm, LDA, ABS_X, STACK_PAGE + stack_size as u16 + 2*i + 1);
        instr16(asm, STA, ABS_X, STACK_PAGE + stack_size as u16 - 2*i - 1);

        // high
        instr16(asm, LDA, ABS_X, STACK_PAGE + stack_size as u16 + 2*i + 2);
        instr16(asm, STA, ABS_X, STACK_PAGE + stack_size as u16 - 2*i);
    }

    for i in 0..body.len() {
        let addr_idx = *op_addresses.items.add(i);
        *(*asm).addresses.items.add(addr_idx) = (*out).count as u16; // update op address

        let op = (*body)[i];
        match op.opcode {
            Op::Bogus => unreachable!("bogus-amogus"),
            Op::Return {arg} => {
                if let Some(arg) = arg {
                    load_arg(asm, arg, op.loc);
                }

                // jump to ret statement
                instr0(asm, JMP, ABS);
                add_reloc(asm, RelocationKind::AddressAbs
                          {idx: *op_addresses.items.add(body.len())});
            },
            Op::Store {index, arg} => {
                load_auto_var(asm, index);
                instr8(asm, STA, ZP, ZP_DEREF_STORE_0);
                instr8(asm, STY, ZP, ZP_DEREF_STORE_1);

                load_arg(asm, arg, op.loc);
                instr(asm, TAX);
                instr(asm, TYA);

                instr8(asm, LDY, IMM, 1);
                instr8(asm, STA, IND_Y, ZP_DEREF_STORE_0); // high
                instr(asm, DEY);
                instr(asm, TXA);
                instr8(asm, STA, IND_Y, ZP_DEREF_STORE_0); // low
            },
            Op::ExternalAssign{name: _, arg: _} => missingf!(op.loc, c!("implement ExternalAssign\n")),
            Op::AutoAssign{index, arg} => {
                load_arg(asm, arg, op.loc);
                store_auto(asm, index);
            },
            Op::Negate {result: _, arg: _} => missingf!(op.loc, c!("implement Negate\n")),
            Op::UnaryNot{result, arg} => {
                load_arg(asm, arg, op.loc);

                instr8(asm, LDX, IMM, 0);

                instr8(asm, CMP, IMM, 0);
                instr8(asm, BNE, REL, 6);

                instr(asm, TYA);
                instr8(asm, CMP, IMM, 0);
                instr8(asm, BNE, REL, 1);

                instr(asm, INX);

                instr(asm, TXA);
                instr8(asm, LDY, IMM, 0);

                store_auto(asm, result);
            },
            Op::Binop {binop, index, lhs, rhs} => {
                match binop {
                    Binop::BitOr => {
                        load_two_args(asm, lhs, rhs, op);

                        instr8(asm, ORA, ZP, ZP_RHS_L);
                        instr(asm, TAX);
                        instr(asm, TYA);
                        instr8(asm, ORA, ZP, ZP_RHS_H);
                        instr(asm, TAY);
                        instr(asm, TXA);
                    },
                    Binop::BitAnd => {
                        load_two_args(asm, lhs, rhs, op);

                        instr8(asm, AND, ZP, ZP_RHS_L);
                        instr(asm, TAX);
                        instr(asm, TYA);
                        instr8(asm, AND, ZP, ZP_RHS_H);
                        instr(asm, TAY);
                        instr(asm, TXA);
                    },
                    Binop::BitShl => missingf!(op.loc, c!("implement BitShl\n")),
                    Binop::BitShr => missingf!(op.loc, c!("implement BitShr\n")),
                    Binop::Plus => {
                        load_two_args(asm, lhs, rhs, op);

                        instr(asm, CLC);
                        instr8(asm, ADC, ZP, ZP_RHS_L);
                        instr(asm, TAX);
                        instr(asm, TYA);
                        instr8(asm, ADC, ZP, ZP_RHS_H);
                        instr(asm, TAY);
                        instr(asm, TXA);
                    },
                    Binop::Minus  => {
                        load_two_args(asm, lhs, rhs, op);

                        instr(asm, SEC);
                        instr8(asm, SBC, ZP, ZP_RHS_L);
                        instr(asm, TAX);
                        instr(asm, TYA);
                        instr8(asm, SBC, ZP, ZP_RHS_H);
                        instr(asm, TAY);
                        instr(asm, TXA);
                    },
                    Binop::Mod => missingf!(op.loc, c!("implement Mod\n")),
                    Binop::Div => {
                        load_two_args(asm, lhs, rhs, op);
                        instr8(asm, STA, ZP, ZP_TMP_0);
                        instr8(asm, STY, ZP, ZP_TMP_1);
                        instr8(asm, LDX, IMM, 0);
                        instr8(asm, STX, ZP, ZP_TMP_2); // low-byte of result
                        instr8(asm, STX, ZP, ZP_TMP_3); // high-byte of result

                        let loop_start = create_address_label_here(asm);
                        let cont = create_address_label(asm);
                        let finished = create_address_label(asm);

                        instr(asm, SEC);
                        instr8(asm, SBC, ZP, ZP_RHS_L);
                        instr8(asm, STA, ZP, ZP_TMP_0);

                        instr8(asm, LDA, ZP, ZP_TMP_1);
                        instr8(asm, SBC, ZP, ZP_RHS_H);
                        instr8(asm, STA, ZP, ZP_TMP_1);

                        instr_label(asm, BMI, REL, finished);
                        add_reloc(asm, RelocationKind::AddressRel{idx: finished});
                        instr0(asm, BEQ, REL);
                        add_reloc(asm, RelocationKind::AddressRel{idx: finished});

                        instr8(asm, LDA, ZP, ZP_TMP_0);
                        instr8(asm, INC, ZP, ZP_TMP_2);
                        instr0(asm, BNE, REL);
                        add_reloc(asm, RelocationKind::AddressRel{idx: cont});
                        instr8(asm, INC, ZP, ZP_TMP_3);

                        link_address_label_here(asm, cont);
                        instr0(asm, JMP, ABS);
                        add_reloc(asm, RelocationKind::AddressAbs{idx: loop_start});

                        link_address_label_here(asm, finished);
                        instr8(asm, LDA, ZP, ZP_TMP_2);
                        instr8(asm, LDY, ZP, ZP_TMP_3);

                    }
                    Binop::Mult => {
                        load_two_args(asm, lhs, rhs, op);

                        // TODO: maybe move this to an intrinsic function,
                        // because it is rather long. Consider this, if we run
                        // out of memory at some point.

                        // shift-and-add/long multiplication
                        // see: https://en.wikipedia.org/wiki/Multiplication_algorithm

                        // TODO: this should be signed, save and restore signes before.

                        // from here on: unsigned multiplication
                        // store lhs
                        instr8(asm, STA, ZP, ZP_TMP_0);
                        instr8(asm, STY, ZP, ZP_TMP_1);

                        // store Y:A in ZP, because shifting and adding is easier
                        // without all the register switching
                        instr8(asm, LDA, IMM, 0);
                        instr8(asm, STA, ZP, ZP_TMP_2);
                        instr8(asm, STA, ZP, ZP_TMP_3);

                        let loop_start = create_address_label_here(asm);
                        let cont = create_address_label(asm);
                        let finished = create_address_label(asm);

                        // if both zero [-> A = 0], we are finished
                        instr8(asm, LDA, ZP, ZP_RHS_L);
                        instr0(asm, BNE, REL);
                        add_reloc(asm, RelocationKind::AddressRel{idx: cont});
                        instr8(asm, LDA, ZP, ZP_RHS_H);
                        instr0(asm, BNE, REL);
                        add_reloc(asm, RelocationKind::AddressRel{idx: cont});

                        instr0(asm, JMP, ABS);
                        add_reloc(asm, RelocationKind::AddressAbs{idx: finished});

                        link_address_label_here(asm, cont);

                        // shift left current accumulater between single adds
                        instr8(asm, ASL, ZP, ZP_TMP_2);
                        instr8(asm, ROL, ZP, ZP_TMP_3);

                        instr8(asm, ASL, ZP, ZP_RHS_L);
                        instr8(asm, ROL, ZP, ZP_RHS_H);

                        // if bit is 0, do not add anything
                        instr0(asm, BCC, REL);
                        add_reloc(asm, RelocationKind::AddressRel{idx: loop_start});

                        // bit is 1 here, we have to add entire lhs to acc
                        instr(asm, CLC);
                        instr8(asm, LDA, ZP, ZP_TMP_2); // acc, low
                        instr8(asm, ADC, ZP, ZP_TMP_0); // lhs, low
                        instr8(asm, STA, ZP, ZP_TMP_2); // acc, low

                        instr8(asm, LDA, ZP, ZP_TMP_3); // acc, high
                        instr8(asm, ADC, ZP, ZP_TMP_1); // lhs, high
                        instr8(asm, STA, ZP, ZP_TMP_3); // acc, high

                        // continue loop
                        instr0(asm, JMP, ABS);
                        add_reloc(asm, RelocationKind::AddressAbs{idx: loop_start});
                        link_address_label_here(asm, finished);

                        // move back in Y:A
                        instr8(asm, LDA, ZP, ZP_TMP_2);
                        instr8(asm, LDY, ZP, ZP_TMP_3);
                    },
                    Binop::Less => {
                        load_two_args(asm, lhs, rhs, op);
                        // we subtract, then check sign

                        instr8(asm, LDX, IMM, 1);

                        instr(asm, SEC); // set carry
                        // sub low byte
                        instr8(asm, SBC, ZP, ZP_RHS_L);
                        // sub high byte
                        instr(asm, TYA);
                        instr8(asm, SBC, ZP, ZP_RHS_H);
                        // high result in A, N flag if less.

                        // if less skip, we already have X=1
                        instr8(asm, BMI, REL, 1);
                        instr(asm, DEX);
                        instr(asm, TXA);
                        // zero extend result
                        instr8(asm, LDY, IMM, 0);
                    },
                    Binop::Greater => {
                        load_two_args(asm, lhs, rhs, op);
                        // we subtract, then check sign

                        instr8(asm, LDX, IMM, 1);

                        // sub low byte
                        instr8(asm, SBC, ZP, ZP_RHS_L);
                        // sub high byte
                        instr(asm, TYA);
                        instr8(asm, SBC, ZP, ZP_RHS_H);
                        // high result in A, N flag if less.

                        // if greater skip, we already have X=1
                        instr8(asm, BPL, REL, 1);

                        instr(asm, DEX);
                        instr(asm, TXA);
                        // zero extend result
                        instr8(asm, LDY, IMM, 0);
                    },
                    Binop::Equal => {
                        load_two_args(asm, lhs, rhs, op);

                        instr8(asm, LDX, IMM, 0);

                        instr8(asm, CMP, ZP, ZP_RHS_L);
                        instr8(asm, BNE, REL, 5);

                        instr8(asm, CPY, ZP, ZP_RHS_H);
                        instr8(asm, BNE, REL, 1);

                        instr(asm, INX);
                        instr(asm, TXA);
                        instr8(asm, LDY, IMM, 0);
                    },
                    Binop::NotEqual => {
                        load_two_args(asm, lhs, rhs, op);

                        instr8(asm, LDX, IMM, 1);

                        instr8(asm, CMP, ZP, ZP_RHS_L);
                        instr8(asm, BNE, REL, 5);

                        instr8(asm, CPY, ZP, ZP_RHS_H);
                        instr8(asm, BNE, REL, 1);

                        instr(asm, DEX);
                        instr(asm, TXA);
                        instr8(asm, LDY, IMM, 0);
                    },
                    Binop::GreaterEqual => {
                        load_two_args(asm, lhs, rhs, op);
                        // we subtract, then check sign

                        instr8(asm, LDX, IMM, 0);

                        instr(asm, SEC); // set carry
                        // sub low byte
                        instr8(asm, SBC, ZP, ZP_RHS_L);
                        // sub high byte
                        instr(asm, TYA);
                        instr8(asm, SBC, ZP, ZP_RHS_H);
                        // high result in A, N flag if less.

                        // if less skip, we already have X=0
                        instr8(asm, BMI, REL, 1);
                        instr(asm, INX);
                        instr(asm, TXA);
                        // zero extend result
                        instr8(asm, LDY, IMM, 0);
                    },
                    Binop::LessEqual => {
                        load_two_args(asm, lhs, rhs, op);
                        // we subtract, then check sign

                        instr8(asm, LDX, IMM, 0);

                        // sub low byte
                        instr8(asm, SBC, ZP, ZP_RHS_L);
                        // sub high byte
                        instr(asm, TYA);
                        instr8(asm, SBC, ZP, ZP_RHS_H);
                        // high result in A, N flag if less.

                        // if greater skip, we already have X=0
                        instr8(asm, BPL, REL, 1);
                        instr(asm, INX);
                        instr(asm, TXA);
                        // zero extend result
                        instr8(asm, LDY, IMM, 0);
                    },
                }
                store_auto(asm, index);
            },
            Op::Funcall{result, fun, args} => {
                match fun {
                    Arg::RefExternal(_) | Arg::External(_) => {},
                    arg => {
                        load_arg(asm, arg, op.loc);
                        instr8(asm, STA, ZP, ZP_DEREF_FUN_0);
                        instr8(asm, STY, ZP, ZP_DEREF_FUN_1);
                    }
                }

                for i in (0..args.count).rev() {
                    load_arg(asm, *args.items.add(i), op.loc);
                    // first arg in Y:A to be compatible with wozmon routines
                    if i != 0 {
                        push16(asm);
                    }
                }
                match fun {
                    Arg::RefExternal(name) | Arg::External(name) => {
                        instr0(asm, JSR, ABS);
                        add_reloc(asm, RelocationKind::Function{name});
                    },
                    _ => { // function pointer already loaded in ZP_DEREF_FUN
                        // there is no jsr (indirect), so emulate using jsr and jmp (indirect).
                        instr16(asm, JSR, ABS, (*asm).code_start + (*out).count as u16 + 6);
                        instr16(asm, JMP, ABS, (*asm).code_start + (*out).count as u16 + 6);
                        instr16(asm, JMP, IND, ZP_DEREF_FUN_0 as u16);
                    },
                }
                if args.count > 1 {
                    instr(asm, TAX);
                    // clear stack
                    for i in 0 .. args.count {
                        if i == 0 {
                            continue;
                        }
                        pop16_discard(asm);
                    }
                    instr(asm, TXA);
                }
                store_auto(asm, result);
            },
            Op::Asm {stmts} => {
                for i in 0..stmts.count {
                    let stmt = *stmts.items.add(i);
                    assemble_statement(out, stmt.line, stmt.loc);
                }
            },
            Op::Label{label} => {
                // TODO: RE: https://github.com/tsoding/b/pull/147#issue-3154667157
                // > For this thing I introduces a new NOP instruction because it would be a bit too
                // > risky to just blindly jump on an address that could possibly be unused.
                //
                // Assess the risk and potentially remove this NOP
                instr(asm, NOP);
                da_append(&mut (*asm).op_labels, Label {
                    func_name: name,
                    label,
                    addr: (*out).count as u16,
                });
            },
            Op::JmpLabel{label} => {
                instr0(asm, JMP, ABS);
                add_reloc(asm, RelocationKind::Label{func_name: name, label});
            },
            Op::JmpIfNotLabel{label, arg} => {
                load_arg(asm, arg, op.loc);

                instr8(asm, CMP, IMM, 0);

                // if !=0, skip next check and branch
                instr8(asm, BNE, REL, 7); // skip next 4 instructions
                instr8(asm, CPY, IMM, 0);
                instr8(asm, BNE, REL, 3);

                instr0(asm, JMP, ABS);
                add_reloc(asm, RelocationKind::Label{func_name: name, label});
            },
        }
    }

    instr8(asm, LDA, IMM, 0);
    instr(asm, TAY);
    let addr_idx = *op_addresses.items.add(body.len());
    *(*asm).addresses.items.add(addr_idx) = (*out).count as u16; // update op address

    if stack_size > 0 {
        // seriously... we don't have enough registers to save A to...
        instr8(asm, STA, ZP, ZP_RHS_L);
        add_sp(asm, stack_size);
        instr8(asm, LDA, ZP, ZP_RHS_L);
    }
    instr(asm, RTS);
}

pub unsafe fn generate_funcs(asm: *mut Assembler, funcs: *const [Func]) {
    for i in 0..funcs.len() {
        generate_function(asm, (*funcs)[i].name, (*funcs)[i].params_count, (*funcs)[i].auto_vars_count, da_slice((*funcs)[i].body));
    }
}

pub unsafe fn apply_relocations(out: *mut String_Builder, data_start: u16, asm: *mut Assembler) {
    'reloc_loop: for i in 0..(*asm).relocs.count {
        let reloc = *(*asm).relocs.items.add(i);
        let caddr = reloc.addr;
        match reloc.kind {
            RelocationKind::DataOffset{off, low} => {
                if low {
                    write_byte_at(out, (data_start + off) as u8, caddr);
                } else {
                    write_byte_at(out, ((data_start + off) >> 8) as u8, caddr);
                }
            },
            RelocationKind::Function{name} => {
                for i in 0..(*asm).functions.count {
                    let label = *(*asm).functions.items.add(i);
                    if strcmp(label.name, name) == 0 {
                        write_word_at(out, (*asm).code_start + label.addr, caddr);
                        continue 'reloc_loop;
                    }
                }
                printf(c!("linking failed. could not find function `%s'\n"), name);
                unreachable!();
            },
            RelocationKind::Label{func_name: name, label} => {
                for i in 0..(*asm).op_labels.count {
                    let op_label = *(*asm).op_labels.items.add(i);
                    if strcmp(op_label.func_name, name) == 0 && op_label.label == label {
                        write_word_at(out, (*asm).code_start + op_label.addr, caddr);
                        continue 'reloc_loop;
                    }
                }
                printf(c!("linking failed. could not find label `%s.%u'\n"), name, label);
                unreachable!();
            },
            RelocationKind::External{name, byte} => {
                for i in 0..(*asm).externals.count {
                    let external = *(*asm).externals.items.add(i);
                    if strcmp(external.name, name) == 0 {
                        match byte {
                            0 => {
                                write_byte_at(out, (((*asm).code_start + external.addr) & 0xFF) as u8, caddr)
                            },
                            1 => {
                                write_byte_at(out, (((*asm).code_start + external.addr) >> 8) as u8, caddr)
                            },
                            2 => {
                                write_word_at(out, (*asm).code_start + external.addr, caddr)
                            },
                            _ => unreachable!(),
                        }
                        continue 'reloc_loop;
                    }
                }
                printf(c!("linking failed. could not find label `%s'\n"), name);
                unreachable!();

            },
            RelocationKind::AddressRel{idx} => {
                let jaddr = *(*asm).addresses.items.add(idx);
                let rel: i16 = jaddr as i16 - (caddr + 1) as i16;
                assert!(rel < 128 && rel >= -128);
                write_byte_at(out, rel as u8, caddr);
            },
            RelocationKind::AddressAbs{idx} => {
                let saddr = *(*asm).addresses.items.add(idx) + (*asm).code_start;
                write_word_at(out, saddr, caddr);
            },
        }
    }
}

pub unsafe fn generate_extrns(asm: *mut Assembler, extrns: *const [*const c_char],
                              funcs: *const [Func], globals: *const [Global]) {
    let out = (*asm).output;
    'skip_function_or_global: for i in 0..extrns.len() {
        // assemble a few "stdlib" functions which can't be programmed in B
        let name = (*extrns)[i];
        for j in 0..funcs.len() {
            let func = (*funcs)[j];
            if strcmp(func.name, name) == 0 {
                continue 'skip_function_or_global
            }
        }
        for j in 0..globals.len() {
            let global = (*globals)[j].name;
            if strcmp(global, name) == 0 {
                continue 'skip_function_or_global
            }
        }
        // TODO: consider introducing target-specific inline assembly and implementing all these intrinsics in it
        if strcmp(name, c!("char")) == 0 {
            // ch = char(string, i);
            // returns the ith character in a string pointed to by string, 0 based

            let fun_addr = (*out).count as u16;
            da_append(&mut (*asm).functions, Function {
                name,
                addr: fun_addr,
            });

            instr(asm, TSX);
            instr(asm, CLC);
            instr16(asm, ADC, ABS_X, STACK_PAGE + 2 + 1); // low

            // load address to buffer in ZP to dereference, because registers
            // only 8 bits
            instr8(asm, STA, ZP, ZP_DEREF_0);

            instr(asm, TYA);
            instr16(asm, ADC, ABS_X, STACK_PAGE + 2 + 2); // high
            instr8(asm, STA, ZP, ZP_DEREF_1);

            instr8(asm, LDX, IMM, 0);

            // A = ((0))
            instr8(asm, LDA, IND_X, ZP_DEREF_0);

            // sign extend Y
            instr8(asm, LDY, IMM, 0);

            instr8(asm, CMP, IMM, 0);
            instr8(asm, BPL, REL, 1);
            instr(asm, DEY);

            instr(asm, RTS);
        } else {
            fprintf(stderr(), c!("Unknown extrn: `%s`, can not link\n"), name);
            abort();
        }
    }
}

pub unsafe fn generate_globals(out: *mut String_Builder, globals: *mut [Global], asm: *mut Assembler) {
    for i in 0..globals.len() {
        let global = (*globals)[i];
        da_append(&mut (*asm).externals, External{
            name: global.name,
            addr: (*out).count as u16,
        });

        if global.values.count > 0 {
            for j in 0..global.values.count {
                match *global.values.items.add(j) {
                    ImmediateValue::Literal(lit) => write_word(out, lit as u16),
                    ImmediateValue::Name(name) => add_reloc(asm, RelocationKind::External{name, byte:2}),
                    ImmediateValue::DataOffset(offset) => {
                        add_reloc(asm, RelocationKind::DataOffset{off: offset as u16, low: true});
                        add_reloc(asm, RelocationKind::DataOffset{off: offset as u16, low: false});
                    }
                }
            }

        }

        if global.values.count < global.minimum_size {
            for _ in 0..(global.minimum_size - global.values.count) {
                write_word(out, 0);
            }
        }
    }
}

pub unsafe fn generate_data_section(out: *mut String_Builder, data: *const [u8]) {
    for i in 0..data.len() {
        write_byte(out, (*data)[i]);
    }
}

pub unsafe fn generate_entry(asm: *mut Assembler) {
    instr0(asm, JSR, ABS);
    add_reloc(asm, RelocationKind::Function{name: c!("main")});

    instr16(asm, JMP, IND, 0xFFFC);
}

pub unsafe fn parse_config_from_link_flags(link_flags: *const[*const c_char]) -> Option<Config> {
    let mut config = Config {
        load_offset: DEFAULT_LOAD_OFFSET,
    };

    // TODO: some sort of help flag to list all these "linker" flags for mos6502
    for i in 0..link_flags.len() {
        let flag = (*link_flags)[i];
        let mut flag_sv = sv_from_cstr(flag);
        let load_offset_prefix = sv_from_cstr(c!("LOAD_OFFSET="));
        if sv_starts_with(flag_sv, load_offset_prefix) {
            flag_sv.data = flag_sv.data.add(load_offset_prefix.count);
            flag_sv.count += load_offset_prefix.count;
            config.load_offset = strtoull(flag_sv.data, ptr::null_mut(), 16) as u16;
        } else {
            fprintf(stderr(), c!("Unknown linker flag: %s\n"), flag);
            return None
        }
    }

    Some(config)
}

pub unsafe fn generate_asm_funcs(asm: *mut Assembler, asm_funcs: *const [AsmFunc]) {
    let out = (*asm).output;
    for i in 0..asm_funcs.len() {
        let asm_func = (*asm_funcs)[i];

        let fun_addr = (*out).count as u16;
        da_append(&mut (*asm).functions, Function {
            name: asm_func.name,
            addr: fun_addr,
        });

        for j in 0..asm_func.body.count {
            let stmt = *asm_func.body.items.add(j);
            assemble_statement(out, stmt.line, stmt.loc);
        }
    }
}

pub unsafe fn generate_program(out: *mut String_Builder, c: *const Compiler, config: Config) -> Option<()> {
    let mut asm: Assembler = zeroed();
    asm.output = out;
    generate_entry(&mut asm);
    asm.code_start = config.load_offset;

    generate_funcs(&mut asm, da_slice((*c).funcs));
    generate_asm_funcs(&mut asm, da_slice((*c).asm_funcs));
    generate_extrns(&mut asm, da_slice((*c).extrns), da_slice((*c).funcs), da_slice((*c).globals));

    let data_start = config.load_offset + (*out).count as u16;
    generate_data_section(out, da_slice((*c).data));
    generate_globals(out, da_slice((*c).globals), &mut asm);

    apply_relocations(out, data_start, &mut asm);
    write_entire_file(c!("./build/test.asm"), asm.assembly.items as *const c_void, asm.assembly.count);
    Some(())
}
