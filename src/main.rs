use std::{
    env,
    error::Error,
    fs::File,
    io::{BufReader, Read},
};

use paste::paste;

macro_rules! instruction {
    ($enum:ident :: $variant:ident, 0) => {
        paste! {
            #[derive(Debug)]
            struct [<$variant Instruction>] {
                size: u8,
            }

            impl [<$variant Instruction>] {
                fn decode(_slice: &[u16]) -> Self {
                    Self {
                        size: 0,
                    }
                }
            }
        }
    };
    ($enum:ident :: $variant:ident, 1) => {
        paste! {
            #[derive(Debug)]
            struct [<$variant Instruction>] {
                size: u8,
                a: u16,
            }

            impl [<$variant Instruction>] {
                fn decode(slice: &[u16]) -> Self {
                    Self {
                        size: 1,
                        a: slice[0],
                    }
                }
            }
        }
    };
    ($enum:ident :: $variant:ident, 2) => {
        paste! {
            #[derive(Debug)]
            struct [<$variant Instruction>] {
                size: u8,
                a: u16,
                b: u16,
            }

            impl [<$variant Instruction>] {
                fn decode(slice: &[u16]) -> Self {
                    Self {
                        size: 2,
                        a: slice[0],
                        b: slice[1],
                    }
                }
            }
        }
    };
    ($enum:ident :: $variant:ident, 3) => {
        paste! {
            #[derive(Debug)]
            struct [<$variant Instruction>] {
                size: u8,
                a: u16,
                b: u16,
                c: u16,
            }

            impl [<$variant Instruction>] {
                fn decode(slice: &[u16]) -> Self {
                    Self {
                        size: 3,
                        a: slice[0],
                        b: slice[1],
                        c: slice[2],
                    }
                }
            }
        }
    };
}

const MAX_MEM: usize = 2u16.pow(15) as usize - 1;
const ADDR_SPACE: usize = MAX_MEM + 8;
const REG_0: usize = ADDR_SPACE - 7;
const REG_1: usize = ADDR_SPACE - 6;
const REG_2: usize = ADDR_SPACE - 5;
const REG_3: usize = ADDR_SPACE - 4;
const REG_4: usize = ADDR_SPACE - 3;
const REG_5: usize = ADDR_SPACE - 2;
const REG_6: usize = ADDR_SPACE - 1;
const REG_7: usize = ADDR_SPACE;

#[derive(Debug)]
struct Machine {
    pc: usize,
    memory: [u16; ADDR_SPACE],
    stack: Vec<u16>,
}

instruction!(OpCode::Halt, 0);
instruction!(OpCode::Set, 2);
instruction!(OpCode::Push, 1);
instruction!(OpCode::Pop, 1);
instruction!(OpCode::Eq, 3);
instruction!(OpCode::Gt, 3);
instruction!(OpCode::Jmp, 1);
instruction!(OpCode::Jt, 2);
instruction!(OpCode::Jf, 2);
instruction!(OpCode::Add, 3);
instruction!(OpCode::Mult, 3);
instruction!(OpCode::Mod, 3);
instruction!(OpCode::And, 3);
instruction!(OpCode::Or, 3);
instruction!(OpCode::Not, 2);
instruction!(OpCode::Rmem, 2);
instruction!(OpCode::Wmem, 2);
instruction!(OpCode::Call, 1);
instruction!(OpCode::Ret, 0);
instruction!(OpCode::Out, 1);
instruction!(OpCode::In, 1);
instruction!(OpCode::Noop, 0);

#[derive(Debug)]
enum Instruction {
    /// 0 - stop execution and terminate the program
    Halt(HaltInstruction),
    /// 1 a b - set register <a> to the value of <b>
    Set(SetInstruction),
    /// 2 a - push <a> onto the stack
    Push(PushInstruction),
    /// 3 a - remove the top element from the stack and write it into <a>; empty stack = error
    Pop(PopInstruction),
    /// 4 a b c - set <a> to 1 if <b> is equal to <c>; set it to 0 otherwise
    Eq(EqInstruction),
    /// 5 a b c - set <a> to 1 if <b> is greater than <c>; set it to 0 otherwise
    Gt(GtInstruction),
    /// 6 a - jump to <a>
    Jmp(JmpInstruction),
    /// 7 a b - if <a> is nonzero, jump to <b>
    Jt(JtInstruction),
    /// 8 a b - if <a> is zero, jump to <b>
    Jf(JfInstruction),
    /// 9 a b c - assign into <a> the sum of <b> and <c> (modulo 32768)
    Add(AddInstruction),
    /// 10 a b c - store into <a> the product of <b> and <c> (modulo 32768)
    Mult(MultInstruction),
    /// 11 a b c - store into <a> the remainder of <b> divided by <c>
    Mod(ModInstruction),
    /// 12 a b c - stores into <a> the bitwise and of <b> and <c>
    And(AndInstruction),
    /// 13 a b c - stores into <a> the bitwise or of <b> and <c>
    Or(OrInstruction),
    /// 14 a b - stores 15-bit bitwise inverse of <b> in <a>
    Not(NotInstruction),
    /// 15 a b - read memory at address <b> and write it to <a>
    Rmem(RmemInstruction),
    /// 16 a b - write the value from <b> into memory at address <a>
    Wmem(WmemInstruction),
    /// 17 a - write the address of the next instruction to the stack and jump to <a>
    Call(CallInstruction),
    /// 18 - remove the top element from the stack and jump to it; empty stack = halt
    Ret(RetInstruction),
    /// 19 a - write the character represented by ascii code <a> to the terminal
    Out(OutInstruction),
    /// 20 a - read a character from the terminal and write its ascii code to <a>; it can
    /// be assumed that once input starts, it will continue until a newline is encountered;
    /// this means that you can safely read whole lines from the keyboard instead of having
    /// to figure out how to read individual characters
    In(InInstruction),
    /// 21 no operation
    Noop(NoopInstruction),
}

#[derive(PartialEq)]
enum OpCode {
    Halt = 0,
    Set = 1,
    Push = 2,
    Pop = 3,
    Eq = 4,
    Gt = 5,
    Jmp = 6,
    Jt = 7,
    Jf = 8,
    Add = 9,
    Mult = 10,
    Mod = 11,
    And = 12,
    Or = 13,
    Not = 14,
    Rmem = 15,
    Wmem = 16,
    Call = 17,
    Ret = 18,
    Out = 19,
    In = 20,
    Noop = 21,
}

impl From<u16> for OpCode {
    fn from(value: u16) -> Self {
        match value {
            0 => OpCode::Halt,
            1 => OpCode::Set,
            2 => OpCode::Pop,
            3 => OpCode::Push,
            4 => OpCode::Eq,
            5 => OpCode::Gt,
            6 => OpCode::Jmp,
            7 => OpCode::Jt,
            8 => OpCode::Jf,
            9 => OpCode::Add,
            10 => OpCode::Mult,
            11 => OpCode::Mod,
            12 => OpCode::And,
            13 => OpCode::Or,
            14 => OpCode::Not,
            15 => OpCode::Rmem,
            16 => OpCode::Wmem,
            17 => OpCode::Call,
            18 => OpCode::Ret,
            19 => OpCode::Out,
            20 => OpCode::In,
            21 => OpCode::Noop,
            _ => panic!("invalid op code {value}"),
        }
    }
}

impl Machine {
    pub fn new() -> Self {
        Self {
            pc: 0,
            memory: [0; ADDR_SPACE],
            stack: Vec::default(),
        }
    }

    pub fn load(&mut self, filename: &str) -> Result<(), std::io::Error> {
        let file = File::open(filename)?;
        let mut reader = BufReader::new(file);
        let mut buf = vec![];
        let _ = reader.read_to_end(&mut buf)?;
        self.load_bytes(&buf)
    }

    pub fn run(mut self) -> Result<(), Box<dyn Error>> {
        loop {
            let inst = self.decode();

            eprintln!("after inst decode - pc: {:?}\tinst: {inst:?}", self.pc);

            match inst {
                Instruction::Noop(_) => continue,
                Instruction::Halt(_) => {
                    break;
                }
                Instruction::Set(_i) => todo!(),
                Instruction::Push(_i) => todo!(),
                Instruction::Pop(_i) => todo!(),
                Instruction::Eq(_i) => todo!(),
                Instruction::Gt(_i) => todo!(),
                Instruction::Jmp(_i) => todo!(),
                Instruction::Jt(_i) => todo!(),
                Instruction::Jf(_i) => todo!(),
                Instruction::Add(_i) => todo!(),
                Instruction::Mult(_i) => todo!(),
                Instruction::Mod(_i) => todo!(),
                Instruction::And(_i) => todo!(),
                Instruction::Or(_i) => todo!(),
                Instruction::Not(_i) => todo!(),
                Instruction::Rmem(_i) => todo!(),
                Instruction::Wmem(_i) => todo!(),
                Instruction::Call(_i) => todo!(),
                Instruction::Ret(_i) => todo!(),
                Instruction::Out(i) => {
                    print!("{}", i.a as u8 as char);
                }
                Instruction::In(_i) => todo!(),
            }
        }
        Ok(())
    }

    fn decode(&mut self) -> Instruction {
        let op = OpCode::from(self.memory[self.pc]);
        self.pc += 1;
        match op {
            OpCode::Halt => {
                let inst = HaltInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Halt(inst)
            }
            OpCode::Set => {
                let inst = SetInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Set(inst)
            }
            OpCode::Push => {
                let inst = PushInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Push(inst)
            }
            OpCode::Pop => {
                let inst = PopInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Pop(inst)
            }
            OpCode::Eq => {
                let inst = EqInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Eq(inst)
            }
            OpCode::Gt => {
                let inst = GtInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Gt(inst)
            }
            OpCode::Jmp => {
                let inst = JmpInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Jmp(inst)
            }
            OpCode::Jt => {
                let inst = JtInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Jt(inst)
            }
            OpCode::Jf => {
                let inst = JfInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Jf(inst)
            }
            OpCode::Add => {
                let inst = AddInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Add(inst)
            }
            OpCode::Mult => {
                let inst = MultInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Mult(inst)
            }
            OpCode::Mod => {
                let inst = ModInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Mod(inst)
            }
            OpCode::And => {
                let inst = AndInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::And(inst)
            }
            OpCode::Or => {
                let inst = OrInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Or(inst)
            }
            OpCode::Not => {
                let inst = NotInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Not(inst)
            }
            OpCode::Rmem => {
                let inst = RmemInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Rmem(inst)
            }
            OpCode::Wmem => {
                let inst = WmemInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Wmem(inst)
            }
            OpCode::Call => {
                let inst = CallInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Call(inst)
            }
            OpCode::Ret => {
                let inst = RetInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Ret(inst)
            }
            OpCode::Out => {
                let inst = OutInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Out(inst)
            }
            OpCode::In => {
                let inst = InInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::In(inst)
            }
            OpCode::Noop => {
                let inst = NoopInstruction::decode(&self.memory[self.pc..]);
                self.pc += usize::from(inst.size);
                Instruction::Noop(inst)
            }
        }
    }

    fn load_bytes(&mut self, buf: &[u8]) -> Result<(), std::io::Error> {
        for (idx, chunk) in buf.chunks_exact(2).enumerate() {
            let word = u16::from_le_bytes([chunk[0], chunk[1]]);
            self.memory[idx] = word;
        }
        Ok(())
    }

    const fn reg_offset(num: u16) -> usize {
        assert!(num < 8);
        MAX_MEM + num as usize
    }

    fn read_reg(&self, num: u16) -> u16 {
        self.memory[Machine::reg_offset(num)]
    }

    fn write_reg(&mut self, num: u16, val: u16) {
        self.memory[Machine::reg_offset(num)] = val;
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = env::args().collect::<Vec<_>>();
    let filename = args[1].as_str();
    let mut vm = Machine::new();
    vm.load(filename)?;
    vm.run()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_param_instruction() {
        let data: &[u16] = &[];
        let halt = HaltInstruction::decode(data);
        let _ = halt;
    }

    #[test]
    fn test_one_param_instruction() {
        let data: &[u16] = &[42];
        let push = PushInstruction::decode(data);
        assert_eq!(push.a, 42);
    }

    #[test]
    fn test_two_param_instruction() {
        let data: &[u16] = &[100, 200];
        let jt = JtInstruction::decode(data);
        assert_eq!(jt.a, 100);
        assert_eq!(jt.b, 200);
    }

    #[test]
    fn test_three_param_instruction() {
        let data: &[u16] = &[1, 2, 3];
        let add = AddInstruction::decode(data);
        assert_eq!(add.a, 1);
        assert_eq!(add.b, 2);
        assert_eq!(add.c, 3);
    }

    #[test]
    fn test_load_program() {
        let program: &[u8] = &[1, 2, 3, 4];
        let mut vm = Machine::new();
        let result = vm.load_bytes(program);
        assert!(result.is_ok());
        assert_eq!(u16::from_le_bytes([1, 2]), vm.memory[0]);
        assert_eq!(u16::from_le_bytes([3, 4]), vm.memory[1]);
    }
}
