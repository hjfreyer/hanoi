pub mod library;
pub mod opcode;
pub mod value;

pub use library::{Library, Sentence, SentenceIndex};
pub use opcode::Instruction;
pub use value::Value;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_display() {
        assert_eq!(format!("{}", Value::Nil), "nil");
        assert_eq!(format!("{}", Value::Bool(true)), "true");
        assert_eq!(format!("{}", Value::Int(42)), "42");
        assert_eq!(format!("{}", Value::Float(3.14)), "3.14");
    }

    #[test]
    fn test_instruction_equality() {
        let inst1 = Instruction::Push(Value::Int(42));
        let inst2 = Instruction::Push(Value::Int(42));
        let inst3 = Instruction::Drop(0);

        assert_eq!(inst1, inst2);
        assert_ne!(inst1, inst3);
    }

    #[test]
    fn test_library_indexing() {
        let mut library = Library::new();
        let sentence1 = vec![
            Instruction::Push(Value::Int(10)),
            Instruction::Drop(0),
        ];
        let sentence2 = vec![
            Instruction::Push(Value::Int(20)),
            Instruction::Drop(0),
        ];

        library.sentences.push(sentence1.clone());
        library.sentences.push(sentence2.clone());

        let idx1 = SentenceIndex::from(0);
        let idx2 = SentenceIndex::from(1);

        assert_eq!(library.sentences[idx1], sentence1);
        assert_eq!(library.sentences[idx2], sentence2);
    }
}
