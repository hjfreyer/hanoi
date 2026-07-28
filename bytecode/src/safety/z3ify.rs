use crate::library::{Library, SentenceIndex, Annotation};
use crate::opcode::Instruction;
use crate::value::Value;
use crate::safety::formula::Expr;
use std::collections::{HashSet, HashMap};

fn get_sentence_name(s_idx: SentenceIndex, library: &Library) -> String {
    let name = &library.names[s_idx];
    if name == "<inline>" {
        let raw: usize = s_idx.into();
        format!("inline_{}", raw)
    } else {
        name.clone()
    }
}

fn resolve_safety_fn(
    annotated_name: &str,
    safety_fn_name: &str,
    library: &Library,
) -> Result<SentenceIndex, String> {
    // 1. Try relative to the annotated sentence's module
    let current_module = if let Some(idx) = annotated_name.rfind("::") {
        &annotated_name[..idx]
    } else {
        ""
    };

    let fq_candidate = if current_module.is_empty() {
        safety_fn_name.to_string()
    } else {
        format!("{}::{}", current_module, safety_fn_name)
    };

    if let Some(pos) = library.names.iter().position(|n| n == &fq_candidate) {
        return Ok(SentenceIndex::from(pos));
    }

    // 2. Try absolute/as-is
    if let Some(pos) = library.names.iter().position(|n| n == safety_fn_name) {
        return Ok(SentenceIndex::from(pos));
    }

    Err(format!(
        "Safety function '{}' not found in library",
        safety_fn_name
    ))
}

pub fn generate_z3ify(library: &Library) -> Result<String, String> {
    // 1. Find all sentences annotated with #[z3ify] or #[safety2]
    let mut z3ify_targets = Vec::new();
    let mut safety2_checks = Vec::new();
    for (s_idx_raw, annotations) in library.annotations.iter().enumerate() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        let has_z3ify = annotations.iter().any(|ann| matches!(ann, Annotation::Z3ify));
        let mut safety2_fn = None;
        for ann in annotations {
            if let Annotation::Safety2(s_fn) = ann {
                safety2_fn = Some(s_fn.clone());
            }
        }

        if has_z3ify {
            z3ify_targets.push(s_idx);
        }

        if let Some(s_fn) = safety2_fn {
            let annotated_name = &library.names[s_idx];
            let safety_fn_idx = resolve_safety_fn(annotated_name, &s_fn, library)?;
            safety2_checks.push((s_idx, safety_fn_idx));
            
            // Implicitly add both functions to targets
            z3ify_targets.push(s_idx);
            z3ify_targets.push(safety_fn_idx);
        }
    }

    // Deduplicate targets
    z3ify_targets.sort();
    z3ify_targets.dedup();

    if z3ify_targets.is_empty() {
        return Err("No sentences annotated with #[z3ify] or #[safety2] were found.".to_string());
    }

    // 2. Cycle detection and transitive dependency collection
    let mut visited = HashSet::new();
    let mut rec_stack = HashSet::new();
    for &s_idx in &z3ify_targets {
        if has_cycle(s_idx, library, &mut visited, &mut rec_stack) {
            return Err(format!(
                "Recursion or cycle detected in dependencies of sentence '{}'. Recursion is not supported by z3ify.",
                get_sentence_name(s_idx, library)
            ));
        }
    }

    // 3. Topological sorting to order dependencies first (DFS post-order)
    let mut ordered_sentences = Vec::new();
    let mut visited_sort = HashSet::new();
    for &s_idx in &z3ify_targets {
        topological_sort(s_idx, library, &mut visited_sort, &mut ordered_sentences);
    }

    // Check that neither the targets nor any dependencies are annotated with #[recursive]
    for &s_idx in &ordered_sentences {
        if library.annotations[s_idx].iter().any(|ann| matches!(ann, Annotation::Recursive)) {
            return Err(format!(
                "Sentence '{}' is annotated with #[recursive] (or is a dependency of a target marked recursive), which is unsupported by z3ify.",
                get_sentence_name(s_idx, library)
            ));
        }
    }

    // 4. Collect tuple sizes used in the program
    let mut tuple_sizes = HashSet::new();
    for sentence in &library.sentences {
        for inst in sentence {
            match inst {
                Instruction::Tuple(n) | Instruction::Untuple(n) => {
                    tuple_sizes.insert(*n);
                }
                Instruction::Push(val) => {
                    collect_tuple_sizes_from_value(val, &mut tuple_sizes);
                }
                _ => {}
            }
        }
    }

    // 5. Collect symbol IDs and names
    let mut symbols_map = HashMap::new();
    for val in library.symbols.values() {
        if let Value::Symbol(sym) = val {
            symbols_map.insert(sym.id, sym.name.clone());
        }
    }
    for sentence in &library.sentences {
        for inst in sentence {
            if let Instruction::Push(val) = inst {
                collect_symbols_from_value(val, &mut symbols_map);
            }
        }
    }
    let mut symbols_list: Vec<(usize, String)> = symbols_map.into_iter().collect();
    symbols_list.sort_by_key(|&(id, _)| id);

    // 6. Generate the Z3 SMT-LIB2 prelude
    let mut output = String::new();
    output.push_str(";; Hanoi SMT-LIB2 Prelude generated by z3ify\n\n");

    // Val and Result datatype definition
    output.push_str("(declare-datatypes () (\n");
    output.push_str("  (Val\n");
    output.push_str("    (ValInt (getInt Int))\n");
    output.push_str("    (ValBool (getBool Bool))\n");
    output.push_str("    (ValFloat (getFloat Int))\n");
    output.push_str("    (ValSymbol (getSymbol Int))\n");
    output.push_str("    (ValTuple0)\n");
    for &n in &tuple_sizes {
        if n == 0 {
            continue;
        }
        output.push_str(&format!("    (ValTuple{} ", n));
        for i in 0..n {
            output.push_str(&format!("(getTuple{}_{} Val) ", n, i));
        }
        output.push_str(")\n");
    }
    output.push_str("  )\n");
    output.push_str("  (Result\n");
    output.push_str("    (Ok (getVal Val))\n");
    output.push_str("    (Panic)\n");
    output.push_str("  )\n");
    output.push_str("))\n\n");

    // Symbol to string mapping function
    output.push_str(";; Symbol to string mapping function\n");
    if symbols_list.is_empty() {
        output.push_str("(define-fun symbol_to_string ((sym_id Int)) String \"\")\n\n");
    } else {
        let mut body = String::new();
        let mut close_parens = 0;
        for (id, name) in &symbols_list {
            body.push_str(&format!(
                "(ite (= sym_id {}) \"{}\" ",
                id,
                escape_smt_string(name)
            ));
            close_parens += 1;
        }
        body.push_str("\"\""); // fallback string
        for _ in 0..close_parens {
            body.push_str(")");
        }
        output.push_str(&format!(
            "(define-fun symbol_to_string ((sym_id Int)) String {})\n\n",
            body
        ));
    }

    output.push_str(";; Tuple helpers for Result\n");
    output.push_str("(define-fun val_tuple0 () Result (Ok ValTuple0))\n");
    for &n in &tuple_sizes {
        if n == 0 {
            continue;
        }
        let mut args_decl = String::new();
        let mut condition = String::new();
        let mut val_args = String::new();
        for i in 0..n {
            args_decl.push_str(&format!("(e{} Result) ", i));
            if i > 0 {
                condition.push_str(" ");
            }
            condition.push_str(&format!("(is-Ok e{})", i));
            val_args.push_str(&format!("(getVal e{}) ", i));
        }
        let condition_wrap = if n == 1 {
            condition
        } else {
            format!("(and {})", condition)
        };
        output.push_str(&format!(
            "(define-fun val_tuple{} ({}) Result (ite {} (Ok (ValTuple{} {})) Panic))\n",
            n, args_decl.trim_end(), condition_wrap, n, val_args.trim_end()
        ));

        for i in 0..n {
            output.push_str(&format!(
                "(define-fun val_getTuple{}_{} ((t Result)) Result (ite (and (is-Ok t) (is-ValTuple{} (getVal t))) (Ok (getTuple{}_{} (getVal t))) Panic))\n",
                n, i, n, n, i
            ));
        }
    }
    output.push_str("\n");

    // Hanoi Primitive Mappings
    output.push_str(";; Primitive Operations\n");
    output.push_str("(define-fun val_add ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValInt (getVal a)) (is-ValInt (getVal b))) (Ok (ValInt (+ (getInt (getVal a)) (getInt (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_sub ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValInt (getVal a)) (is-ValInt (getVal b))) (Ok (ValInt (- (getInt (getVal a)) (getInt (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_mul ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValInt (getVal a)) (is-ValInt (getVal b))) (Ok (ValInt (* (getInt (getVal a)) (getInt (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_div ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValInt (getVal a)) (is-ValInt (getVal b))) (Ok (ValInt (div (getInt (getVal a)) (getInt (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_mod ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValInt (getVal a)) (is-ValInt (getVal b))) (Ok (ValInt (mod (getInt (getVal a)) (getInt (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_neg ((a Result)) Result (ite (and (is-Ok a) (is-ValInt (getVal a))) (Ok (ValInt (- (getInt (getVal a))))) Panic))\n");
    output.push_str("(define-fun val_not ((a Result)) Result (ite (and (is-Ok a) (is-ValBool (getVal a))) (Ok (ValBool (not (getBool (getVal a))))) Panic))\n");
    output.push_str("(define-fun val_equal ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b)) (Ok (ValBool (= (getVal a) (getVal b)))) Panic))\n");
    output.push_str("(define-fun val_less ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValInt (getVal a)) (is-ValInt (getVal b))) (Ok (ValBool (< (getInt (getVal a)) (getInt (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_greater ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValInt (getVal a)) (is-ValInt (getVal b))) (Ok (ValBool (> (getInt (getVal a)) (getInt (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_and ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValBool (getVal a)) (is-ValBool (getVal b))) (Ok (ValBool (and (getBool (getVal a)) (getBool (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_or ((a Result) (b Result)) Result (ite (and (is-Ok a) (is-Ok b) (is-ValBool (getVal a)) (is-ValBool (getVal b))) (Ok (ValBool (or (getBool (getVal a)) (getBool (getVal b))))) Panic))\n");
    output.push_str("(define-fun val_is_int ((a Result)) Result (ite (is-Ok a) (Ok (ValBool (is-ValInt (getVal a)))) Panic))\n");
    output.push_str("(define-fun val_is_bool ((a Result)) Result (ite (is-Ok a) (Ok (ValBool (is-ValBool (getVal a)))) Panic))\n");
    output.push_str("(define-fun val_is_symbol ((a Result)) Result (ite (is-Ok a) (Ok (ValBool (is-ValSymbol (getVal a)))) Panic))\n");
    output.push_str("(define-fun val_is_float ((a Result)) Result (ite (is-Ok a) (Ok (ValBool (is-ValFloat (getVal a)))) Panic))\n");
    output.push_str("(define-fun val_is_numeric ((a Result)) Result (ite (is-Ok a) (Ok (ValBool (or (is-ValInt (getVal a)) (is-ValFloat (getVal a))))) Panic))\n");

    let mut tuple_checks = vec!["(is-ValTuple0 (getVal a))".to_string()];
    let mut length_cases = vec!["(ite (is-ValTuple0 (getVal a)) 0".to_string()];
    for &n in &tuple_sizes {
        if n == 0 { continue; }
        tuple_checks.push(format!("(is-ValTuple{} (getVal a))", n));
        length_cases.push(format!("(ite (is-ValTuple{} (getVal a)) {}", n, n));
    }
    let is_tuple_or_chain = if tuple_checks.len() == 1 {
        tuple_checks[0].clone()
    } else {
        format!("(or {})", tuple_checks.join(" "))
    };
    let mut length_ite = "0".to_string();
    for case in length_cases.iter().rev() {
        length_ite = format!("{} {})", case, length_ite);
    }
    output.push_str(&format!(
        "(define-fun val_is_tuple ((a Result)) Result (ite (is-Ok a) (Ok (ValBool {})) Panic))\n",
        is_tuple_or_chain
    ));
    output.push_str(&format!(
        "(define-fun val_tuple_length ((a Result)) Result (ite (and (is-Ok a) (is-Ok (val_is_tuple a)) (getBool (getVal (val_is_tuple a)))) (Ok (ValInt {})) Panic))\n",
        length_ite
    ));
    output.push_str("(define-fun val_symbol_len ((a Result)) Result (ite (and (is-Ok a) (is-ValSymbol (getVal a))) (Ok (ValInt (str.len (symbol_to_string (getSymbol (getVal a)))))) Panic))\n");
    output.push_str("(define-fun val_symbol_char_at ((sym Result) (idx Result)) Result (ite (and (is-Ok sym) (is-Ok idx) (is-ValSymbol (getVal sym)) (is-ValInt (getVal idx))) (Ok (ValInt (str.to_code (str.at (symbol_to_string (getSymbol (getVal sym))) (getInt (getVal idx)))))) Panic))\n");
    output.push_str("(define-fun val_cond ((c Result) (t Result) (e Result)) Result (ite (and (is-Ok c) (is-ValBool (getVal c))) (ite (getBool (getVal c)) t e) Panic))\n");
    output.push_str("(define-fun val_is_true ((c Result)) Bool (and (is-Ok c) (is-ValBool (getVal c)) (getBool (getVal c))))\n\n");

    // 7. Translate sentences in topological order
    let mut arity_map = HashMap::new();
    let mut float_to_id = HashMap::new();

    output.push_str(";; Translated Sentences\n");
    for s_idx in ordered_sentences {
        let (def_smt, (n, m)) = translate_sentence(s_idx, library, &arity_map, &mut float_to_id)?;
        arity_map.insert(s_idx, (n, m));
        output.push_str(&def_smt);
        output.push_str("\n");
    }

    // 8. Generate Safety2 Check Sections
    if !safety2_checks.is_empty() {
        output.push_str(";; Safety2 Checks\n");
        for (annotated_idx, safety_idx) in safety2_checks {
            let annotated_name = get_sentence_name(annotated_idx, library);
            let safety_name = get_sentence_name(safety_idx, library);

            let (n_safety, m_safety) = arity_map[&safety_idx];
            let (n_annotated, m_annotated) = arity_map[&annotated_idx];

            if n_safety != 1 || m_safety != 1 {
                return Err(format!(
                    "Safety function '{}' must have arity 1 -> 1, but has {} -> {}",
                    safety_name, n_safety, m_safety
                ));
            }
            if n_annotated != 1 {
                return Err(format!(
                    "Annotated function '{}' must have 1 input, but has {}",
                    annotated_name, n_annotated
                ));
            }
            if m_annotated == 0 {
                return Err(format!(
                    "Annotated function '{}' must have at least 1 output to be verified via z3ify",
                    annotated_name
                ));
            }

            output.push_str(&format!(
                ";; Verify that '{}' never panics when '{}' returns true\n",
                annotated_name, safety_name
            ));
            output.push_str("(push)\n");
            output.push_str(" (declare-const x Val)\n");
            output.push_str(&format!(
                " (assert (= (|{}_out_0| (Ok x)) (Ok (ValBool true))))\n",
                safety_name
            ));
            output.push_str(&format!(
                " (assert (is-Panic (|{}_out_0| (Ok x))))\n",
                annotated_name
            ));
            output.push_str(" (check-sat)\n");
            output.push_str("(pop)\n\n");
        }
    }

    Ok(output)
}

fn has_cycle(
    s_idx: SentenceIndex,
    library: &Library,
    visited: &mut HashSet<SentenceIndex>,
    rec_stack: &mut HashSet<SentenceIndex>,
) -> bool {
    if rec_stack.contains(&s_idx) {
        return true;
    }
    if visited.contains(&s_idx) {
        return false;
    }
    visited.insert(s_idx);
    rec_stack.insert(s_idx);
    for inst in &library.sentences[s_idx] {
        match inst {
            Instruction::Jump(target) => {
                if has_cycle(*target, library, visited, rec_stack) {
                    return true;
                }
            }
            Instruction::Branch(then_t, else_t) => {
                if has_cycle(*then_t, library, visited, rec_stack) {
                    return true;
                }
                if has_cycle(*else_t, library, visited, rec_stack) {
                    return true;
                }
            }
            _ => {}
        }
    }
    rec_stack.remove(&s_idx);
    false
}

fn topological_sort(
    s_idx: SentenceIndex,
    library: &Library,
    visited: &mut HashSet<SentenceIndex>,
    order: &mut Vec<SentenceIndex>,
) {
    if visited.contains(&s_idx) {
        return;
    }
    visited.insert(s_idx);
    for inst in &library.sentences[s_idx] {
        match inst {
            Instruction::Jump(target) => {
                topological_sort(*target, library, visited, order);
            }
            Instruction::Branch(then_t, else_t) => {
                topological_sort(*then_t, library, visited, order);
                topological_sort(*else_t, library, visited, order);
            }
            _ => {}
        }
    }
    order.push(s_idx);
}

fn collect_tuple_sizes_from_value(val: &Value, sizes: &mut HashSet<usize>) {
    if let Value::Tuple(elements) = val {
        sizes.insert(elements.len());
        for elem in elements {
            collect_tuple_sizes_from_value(elem, sizes);
        }
    }
}

fn collect_symbols_from_value(val: &Value, map: &mut HashMap<usize, String>) {
    match val {
        Value::Symbol(sym) => {
            map.insert(sym.id, sym.name.clone());
        }
        Value::Tuple(elements) => {
            for elem in elements {
                collect_symbols_from_value(elem, map);
            }
        }
        _ => {}
    }
}

fn escape_smt_string(s: &str) -> String {
    let mut escaped = String::new();
    for c in s.chars() {
        if c == '"' {
            escaped.push_str("\"\"");
        } else if c == '\\' {
            escaped.push_str("\\u{5c}");
        } else if c.is_ascii() && !c.is_ascii_control() {
            escaped.push(c);
        } else {
            escaped.push_str(&format!("\\u{{{:x}}}", c as u32));
        }
    }
    escaped
}

struct Step {
    bindings: Vec<(String, Expr)>,
}

fn ensure_stack_depth_ssa(
    stack: &mut Vec<String>,
    required_depth: usize,
    inputs_needed: &mut usize,
    step_0_bindings: &mut Vec<(String, Expr)>,
) {
    if stack.len() < required_depth {
        let diff = required_depth - stack.len();
        for _ in 0..diff {
            let var_name = format!("in_{}", *inputs_needed);
            let stack_var = format!("s_0_{}", *inputs_needed);
            *inputs_needed += 1;
            
            step_0_bindings.push((stack_var.clone(), Expr::Var(var_name)));
            stack.insert(0, stack_var);
        }
    }
}

fn val_to_expr(val: &Value) -> Expr {
    let val_expr = val_to_expr_raw(val);
    Expr::Call("Ok".to_string(), vec![val_expr])
}

fn val_to_expr_raw(val: &Value) -> Expr {
    match val {
        Value::Bool(b) => Expr::Call("ValBool".to_string(), vec![Expr::Bool(*b)]),
        Value::Int(i) => Expr::Call("ValInt".to_string(), vec![Expr::Int(*i)]),
        Value::Float(f) => Expr::Call("ValFloat".to_string(), vec![Expr::Float(f.to_string())]),
        Value::Symbol(sym) => Expr::Call("ValSymbol".to_string(), vec![Expr::Int(sym.id as i64)]),
        Value::Tuple(elements) => {
            let elms = elements.iter().map(val_to_expr_raw).collect();
            let n = elements.len();
            if n == 0 {
                Expr::Call("ValTuple0".to_string(), vec![])
            } else {
                Expr::Call(format!("ValTuple{}", n), elms)
            }
        }
    }
}

fn get_declared_arity(s_idx: SentenceIndex, library: &Library) -> Option<(usize, usize)> {
    for ann in &library.annotations[s_idx] {
        if let Annotation::Arity(n, m) = ann {
            return Some((*n as usize, *m as usize));
        }
    }
    None
}

fn format_nested_lets(
    steps: &[Step],
    step_idx: usize,
    final_body: &str,
    float_to_id: &mut HashMap<String, usize>,
) -> String {
    if step_idx >= steps.len() {
        return final_body.to_string();
    }
    let step = &steps[step_idx];
    let mut bindings_str = String::new();
    for (var, expr) in &step.bindings {
        bindings_str.push_str(&format!("({} {}) ", var, expr_to_smt(expr, float_to_id)));
    }
    let inner = format_nested_lets(steps, step_idx + 1, final_body, float_to_id);
    format!("(let ({}) {})", bindings_str.trim_end(), inner)
}

fn translate_sentence(
    s_idx: SentenceIndex,
    library: &Library,
    arity_map: &HashMap<SentenceIndex, (usize, usize)>,
    float_to_id: &mut HashMap<String, usize>,
) -> Result<(String, (usize, usize)), String> {
    let name = get_sentence_name(s_idx, library);
    let sentence = &library.sentences[s_idx];

    let (declared_in, _declared_out) = get_declared_arity(s_idx, library).unwrap_or_else(|| {
        if let Some(Some(arities)) = library.instruction_arities.get(s_idx) {
            if !arities.is_empty() {
                return (arities[0].inputs() as usize, 0);
            }
        }
        (0, 0)
    });

    let mut steps = Vec::new();
    let mut stack = Vec::new();
    
    // Initial bindings for Step 0:
    let mut initial_bindings = vec![("ok_0".to_string(), Expr::Bool(true))];
    for i in 0..declared_in {
        let in_var = format!("in_{}", i);
        let stack_var = format!("s_0_{}", i);
        initial_bindings.push((stack_var.clone(), Expr::Var(in_var)));
        stack.push(stack_var);
    }
    steps.push(Step { bindings: initial_bindings });
    
    let mut ok_var = "ok_0".to_string();
    let mut inputs_needed = declared_in;
    let mut step_idx = 1;

    for inst in sentence {
        let prev_ok = ok_var.clone();
        ok_var = format!("ok_{}", step_idx);
        let mut bindings = Vec::new();

        match inst {
            Instruction::Push(val) => {
                let stack_var = format!("s_{}_0", step_idx);
                bindings.push((stack_var.clone(), val_to_expr(val)));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::Drop(n) => {
                ensure_stack_depth_ssa(&mut stack, n + 1, &mut inputs_needed, &mut steps[0].bindings);
                stack.remove(stack.len() - 1 - n);
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
            }
            Instruction::Pick(n) => {
                ensure_stack_depth_ssa(&mut stack, n + 1, &mut inputs_needed, &mut steps[0].bindings);
                let val_var = stack[stack.len() - 1 - n].clone();
                let stack_var = format!("s_{}_0", step_idx);
                bindings.push((stack_var.clone(), Expr::Var(val_var)));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::Roll(n) => {
                ensure_stack_depth_ssa(&mut stack, n + 1, &mut inputs_needed, &mut steps[0].bindings);
                let val_var = stack.remove(stack.len() - 1 - n);
                let stack_var = format!("s_{}_0", step_idx);
                bindings.push((stack_var.clone(), Expr::Var(val_var)));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::Equal | Instruction::Greater | Instruction::Less |
            Instruction::Add | Instruction::Subtract | Instruction::Multiply |
            Instruction::Divide | Instruction::Modulo | Instruction::And | Instruction::Or => {
                ensure_stack_depth_ssa(&mut stack, 2, &mut inputs_needed, &mut steps[0].bindings);
                let b_var = stack.pop().unwrap();
                let a_var = stack.pop().unwrap();
                let op = match inst {
                    Instruction::Equal => "val_equal",
                    Instruction::Greater => "val_greater",
                    Instruction::Less => "val_less",
                    Instruction::Add => "val_add",
                    Instruction::Subtract => "val_sub",
                    Instruction::Multiply => "val_mul",
                    Instruction::Divide => "val_div",
                    Instruction::Modulo => "val_mod",
                    Instruction::And => "val_and",
                    Instruction::Or => "val_or",
                    _ => unreachable!(),
                };
                let stack_var = format!("s_{}_0", step_idx);
                bindings.push((stack_var.clone(), Expr::Call(op.to_string(), vec![Expr::Var(a_var), Expr::Var(b_var)])));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::Not | Instruction::Negate => {
                ensure_stack_depth_ssa(&mut stack, 1, &mut inputs_needed, &mut steps[0].bindings);
                let a_var = stack.pop().unwrap();
                let op = match inst {
                    Instruction::Not => "val_not",
                    Instruction::Negate => "val_neg",
                    _ => unreachable!(),
                };
                let stack_var = format!("s_{}_0", step_idx);
                bindings.push((stack_var.clone(), Expr::Call(op.to_string(), vec![Expr::Var(a_var)])));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::Print => {
                ensure_stack_depth_ssa(&mut stack, 1, &mut inputs_needed, &mut steps[0].bindings);
                stack.pop();
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
            }
            Instruction::Panic => {
                bindings.push((ok_var.clone(), Expr::Bool(false)));
            }
            Instruction::Assert => {
                ensure_stack_depth_ssa(&mut stack, 1, &mut inputs_needed, &mut steps[0].bindings);
                let cond_var = stack.pop().unwrap();
                bindings.push((
                    ok_var.clone(),
                    Expr::Call(
                        "and".to_string(),
                        vec![
                            Expr::Var(prev_ok),
                            Expr::Call("val_is_true".to_string(), vec![Expr::Var(cond_var)]),
                        ],
                    ),
                ));
            }
            Instruction::AssertEqual => {
                ensure_stack_depth_ssa(&mut stack, 2, &mut inputs_needed, &mut steps[0].bindings);
                let b_var = stack.pop().unwrap();
                let a_var = stack.pop().unwrap();
                let eq = Expr::Call("val_equal".to_string(), vec![Expr::Var(a_var), Expr::Var(b_var)]);
                bindings.push((
                    ok_var.clone(),
                    Expr::Call(
                        "and".to_string(),
                        vec![
                            Expr::Var(prev_ok),
                            Expr::Call("val_is_true".to_string(), vec![eq]),
                        ],
                    ),
                ));
            }
            Instruction::Tuple(n) => {
                ensure_stack_depth_ssa(&mut stack, *n, &mut inputs_needed, &mut steps[0].bindings);
                let mut elms = Vec::new();
                for _ in 0..*n {
                    elms.push(Expr::Var(stack.pop().unwrap()));
                }
                let stack_var = format!("s_{}_0", step_idx);
                let op = if *n == 0 {
                    Expr::Call("val_tuple0".to_string(), vec![])
                } else {
                    Expr::Call(format!("val_tuple{}", n), elms)
                };
                bindings.push((stack_var.clone(), op));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::Untuple(n) => {
                ensure_stack_depth_ssa(&mut stack, 1, &mut inputs_needed, &mut steps[0].bindings);
                let t_var = stack.pop().unwrap();
                for i in (0..*n).rev() {
                    let stack_var = format!("s_{}_{}", step_idx, i);
                    let op = Expr::Call(format!("val_getTuple{}_{}", n, i), vec![Expr::Var(t_var.clone())]);
                    bindings.push((stack_var.clone(), op));
                    stack.push(stack_var);
                }
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
            }
            Instruction::SymbolLen => {
                ensure_stack_depth_ssa(&mut stack, 1, &mut inputs_needed, &mut steps[0].bindings);
                let sym_var = stack.pop().unwrap();
                let stack_var = format!("s_{}_0", step_idx);
                bindings.push((stack_var.clone(), Expr::Call("val_symbol_len".to_string(), vec![Expr::Var(sym_var)])));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::IsInt | Instruction::IsBool | Instruction::IsFloat |
            Instruction::IsSymbol | Instruction::IsTuple | Instruction::TupleLength => {
                ensure_stack_depth_ssa(&mut stack, 1, &mut inputs_needed, &mut steps[0].bindings);
                let val_var = stack.pop().unwrap();
                let stack_var = format!("s_{}_0", step_idx);
                let op = match inst {
                    Instruction::IsInt => "val_is_int",
                    Instruction::IsBool => "val_is_bool",
                    Instruction::IsFloat => "val_is_float",
                    Instruction::IsSymbol => "val_is_symbol",
                    Instruction::IsTuple => "val_is_tuple",
                    Instruction::TupleLength => "val_tuple_length",
                    _ => unreachable!(),
                };
                bindings.push((stack_var.clone(), Expr::Call(op.to_string(), vec![Expr::Var(val_var)])));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::SymbolCharAt => {
                ensure_stack_depth_ssa(&mut stack, 2, &mut inputs_needed, &mut steps[0].bindings);
                let idx_var = stack.pop().unwrap();
                let sym_var = stack.pop().unwrap();
                let stack_var = format!("s_{}_0", step_idx);
                bindings.push((stack_var.clone(), Expr::Call("val_symbol_char_at".to_string(), vec![Expr::Var(sym_var), Expr::Var(idx_var)])));
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
                stack.push(stack_var);
            }
            Instruction::Jump(target) => {
                let &(n_t, m_t) = arity_map.get(target).ok_or_else(|| {
                    format!("Internal error: dependency sentence arity not found for jump to target {:?}", target)
                })?;
                ensure_stack_depth_ssa(&mut stack, n_t, &mut inputs_needed, &mut steps[0].bindings);
                let mut args = Vec::new();
                for _ in 0..n_t {
                    args.push(Expr::Var(stack.pop().unwrap()));
                }
                args.reverse();
                let target_name = get_sentence_name(*target, library);
                for i in (0..m_t).rev() {
                    let stack_var = format!("s_{}_{}", step_idx, i);
                    let op = Expr::Call(format!("|{}_out_{}|", target_name, i), args.clone());
                    bindings.push((stack_var.clone(), op));
                    stack.push(stack_var);
                }
                bindings.push((ok_var.clone(), Expr::Var(prev_ok)));
            }
            Instruction::Branch(then_t, else_t) => {
                ensure_stack_depth_ssa(&mut stack, 1, &mut inputs_needed, &mut steps[0].bindings);
                let cond_var = stack.pop().unwrap();

                let &(n_then, m_then) = arity_map.get(then_t).ok_or_else(|| {
                    format!("Internal error: dependency sentence arity not found for branch target {:?}", then_t)
                })?;
                let &(n_else, m_else) = arity_map.get(else_t).ok_or_else(|| {
                    format!("Internal error: dependency sentence arity not found for branch target {:?}", else_t)
                })?;

                let max_n = std::cmp::max(n_then, n_else);
                ensure_stack_depth_ssa(&mut stack, max_n, &mut inputs_needed, &mut steps[0].bindings);

                let mut then_args = Vec::new();
                for i in (stack.len() - n_then)..stack.len() {
                    then_args.push(Expr::Var(stack[i].clone()));
                }

                let mut else_args = Vec::new();
                for i in (stack.len() - n_else)..stack.len() {
                    else_args.push(Expr::Var(stack[i].clone()));
                }

                for _ in 0..max_n {
                    stack.pop();
                }

                let then_name = get_sentence_name(*then_t, library);
                let else_name = get_sentence_name(*else_t, library);

                let max_m = std::cmp::max(m_then, m_else);

                for i in (0..max_m).rev() {
                    let stack_var = format!("s_{}_{}", step_idx, i);
                    let then_expr = if i < m_then {
                        Expr::Call(format!("|{}_out_{}|", then_name, i), then_args.clone())
                    } else {
                        Expr::Call("Panic".to_string(), vec![])
                    };
                    let else_expr = if i < m_else {
                        Expr::Call(format!("|{}_out_{}|", else_name, i), else_args.clone())
                    } else {
                        Expr::Call("Panic".to_string(), vec![])
                    };
                    let cond_expr = Expr::Cond(
                        Box::new(Expr::Var(cond_var.clone())),
                        Box::new(then_expr),
                        Box::new(else_expr)
                    );
                    bindings.push((stack_var.clone(), cond_expr));
                    stack.push(stack_var);
                }

                bindings.push((
                    ok_var.clone(),
                    Expr::Call(
                        "and".to_string(),
                        vec![
                            Expr::Var(prev_ok),
                            Expr::Call("is-Ok".to_string(), vec![Expr::Var(cond_var)]),
                        ],
                    ),
                ));
            }
        }

        steps.push(Step { bindings });
        step_idx += 1;
    }

    let n = inputs_needed;
    let m = stack.len();

    let mut args_str = String::new();
    for i in 0..n {
        args_str.push_str(&format!("(in_{} Result) ", i));
    }
    let args_str = args_str.trim_end();

    let mut definitions = String::new();
    for i in 0..m {
        let expr_var = &stack[stack.len() - 1 - i];
        let final_body = format!("(ite {} {} Panic)", ok_var, expr_var);
        let nested_body = format_nested_lets(&steps, 0, &final_body, float_to_id);

        definitions.push_str(&format!(
            "(define-fun |{}_out_{}| ({}) Result {})\n",
            name, i, args_str, nested_body
        ));
    }

    Ok((definitions, (n, m)))
}

fn expr_to_smt(expr: &Expr, float_to_id: &mut HashMap<String, usize>) -> String {
    match expr {
        Expr::Int(val) => format!("{}", val),
        Expr::Bool(val) => format!("{}", val),
        Expr::Float(f) => {
            let next_id = float_to_id.len();
            let id = *float_to_id.entry(f.clone()).or_insert(next_id);
            format!("{}", id)
        }
        Expr::Var(name) => {
            if name.contains("::") {
                format!("|{}|", name)
            } else {
                name.clone()
            }
        }
        Expr::Call(name, args) => {
            let args_smt: Vec<String> = args.iter().map(|arg| expr_to_smt(arg, float_to_id)).collect();
            if args_smt.is_empty() {
                name.clone()
            } else {
                format!("({} {})", name, args_smt.join(" "))
            }
        }
        Expr::Cond(c, t, e) => {
            // (val_cond c t e)
            format!(
                "(val_cond {} {} {})",
                expr_to_smt(c, float_to_id),
                expr_to_smt(t, float_to_id),
                expr_to_smt(e, float_to_id)
            )
        }
        _ => panic!("Internal error: unexpected AST expression in z3ify translation: {:?}", expr),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assembly::assemble;

    #[test]
    fn test_safety2_z3ify_generation() {
        let code = r#"
            #[arity(1, 1)]
            sentence safe_for_foo {
                is_int
            }

            #[arity(1, 1)]
            #[safety2(safe_for_foo)]
            sentence foo {
                push 1
                add
            }
        "#;
        let library = assemble(code).unwrap();
        let smt = generate_z3ify(&library).unwrap();

        // Check that both functions were translated
        assert!(smt.contains("define-fun |safe_for_foo_out_0|"));
        assert!(smt.contains("define-fun |foo_out_0|"));

        // Check that the safety2 check block is present
        assert!(smt.contains(";; Safety2 Checks"));
        assert!(smt.contains("Verify that 'foo' never panics when 'safe_for_foo' returns true"));
        assert!(smt.contains("(push)"));
        assert!(smt.contains("(declare-const x Val)"));
        assert!(smt.contains("(assert (= (|safe_for_foo_out_0| (Ok x)) (Ok (ValBool true))))"));
        assert!(smt.contains("(assert (is-Panic (|foo_out_0| (Ok x))))"));
        assert!(smt.contains("(check-sat)"));
        assert!(smt.contains("(pop)"));
    }

    #[test]
    fn test_safety2_invalid_arity() {
        let code = r#"
            #[arity(2, 1)]
            sentence safe_invalid {
                add
            }

            #[arity(1, 1)]
            #[safety2(safe_invalid)]
            sentence foo {
                drop 0
                push 1
            }
        "#;
        let library = assemble(code).unwrap();
        let res = generate_z3ify(&library);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Safety function 'safe_invalid' must have arity 1 -> 1"));
    }
}
