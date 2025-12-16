use anyhow::{Context, Result};
use hanoi::bytecode::debuginfo::{
    Library as DebuginfoLibrary, Position, Sentence as DebuginfoSentence, Span,
    Word as DebuginfoWord,
};
use hanoi::bytecode::Library as BytecodeLibrary;
use json_spanned_value::spanned::Spanned;
use json_spanned_value::{from_str, Value as SpannedValue};
use serde_json::Value as JsonValue;
use std::fs;
use std::ops::Deref;
use std::path::PathBuf;

fn byte_to_line_col(text: &str, byte_pos: usize) -> Position {
    let mut line = 1;
    let mut col = 1;
    let mut bytes = 0;

    for ch in text.chars() {
        if bytes >= byte_pos {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
        bytes += ch.len_utf8();
    }

    Position { line, col }
}

fn extract_sentence_word_spans(
    json_value: &Spanned<SpannedValue>,
    sentence_idx: usize,
) -> Option<Vec<(usize, usize)>> {
    // Use Deref to get the inner value
    let value: &SpannedValue = json_value.deref();

    // Navigate to sentences array
    let sentences_span = match value {
        SpannedValue::Object(map) => map
            .iter()
            .find(|(k, _)| k.deref().deref() == "sentences")
            .map(|(_, v)| v),
        _ => None,
    }?;

    // Navigate to the specific sentence
    let sentence_span = match sentences_span.deref() {
        SpannedValue::Array(arr) => arr.get(sentence_idx),
        _ => None,
    }?;

    // Navigate to words array
    let words_span = match sentence_span.deref() {
        SpannedValue::Object(map) => map
            .iter()
            .find(|(k, _)| k.deref().deref() == "words")
            .map(|(_, v)| v),
        _ => None,
    }?;

    // Extract spans for each word
    let mut spans = Vec::new();
    match words_span.deref() {
        SpannedValue::Array(word_arr) => {
            for word in word_arr {
                spans.push((word.start(), word.end()));
            }
        }
        _ => return None,
    }

    Some(spans)
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: debugc <input.json> <output.json>");
        std::process::exit(1);
    }

    let input_path = PathBuf::from(&args[1]);
    let output_path = PathBuf::from(&args[2]);

    // Read the input JSON file
    let json_text = fs::read_to_string(&input_path)
        .with_context(|| format!("Failed to read input file: {}", input_path.display()))?;

    // Parse with json-spanned-value to get spans
    let spanned_json: Spanned<SpannedValue> =
        from_str(&json_text).context("Failed to parse JSON with spans")?;

    // Deserialize as bytecode::Library
    let json_value: JsonValue =
        serde_json::from_str(&json_text).context("Failed to deserialize JSON")?;

    let bytecode_lib: BytecodeLibrary =
        serde_json::from_value(json_value).context("Failed to deserialize as bytecode::Library")?;

    // Extract file path from input
    let file_path = input_path
        .canonicalize()
        .unwrap_or_else(|_| input_path.clone());

    // Build debuginfo::Library
    let mut debuginfo_sentences = Vec::new();

    for (sentence_idx, sentence) in bytecode_lib.sentences.iter().enumerate() {
        let word_spans = extract_sentence_word_spans(&spanned_json, sentence_idx);

        let mut debuginfo_words = Vec::new();
        for (word_idx, _word) in sentence.words.iter().enumerate() {
            let span = if let Some(ref spans) = word_spans {
                if let Some(&(start, end)) = spans.get(word_idx) {
                    let begin = byte_to_line_col(&json_text, start);
                    let end_pos = byte_to_line_col(&json_text, end);
                    Some(Span {
                        file: file_path.clone(),
                        begin,
                        end: end_pos,
                    })
                } else {
                    None
                }
            } else {
                None
            };

            debuginfo_words.push(DebuginfoWord { span });
        }

        debuginfo_sentences.push(DebuginfoSentence {
            words: debuginfo_words,
        });
    }

    let debuginfo_lib = DebuginfoLibrary {
        sentences: debuginfo_sentences,
    };

    // Write the output JSON file
    let output_json = serde_json::to_string_pretty(&debuginfo_lib)
        .context("Failed to serialize debuginfo::Library")?;

    fs::write(&output_path, output_json)
        .with_context(|| format!("Failed to write output file: {}", output_path.display()))?;

    println!(
        "Successfully generated debug info: {}",
        output_path.display()
    );

    Ok(())
}
