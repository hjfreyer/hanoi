use crate::library::{Library, SentenceIndex, Annotation};
use crate::opcode::Instruction;
use crate::value::Value;
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
    let mut resolved_segments: Vec<String> = if let Some(idx) = annotated_name.rfind("::") {
        annotated_name[..idx].split("::").map(|s| s.to_string()).collect()
    } else {
        Vec::new()
    };

    let target_segments: Vec<&str> = safety_fn_name.split("::").collect();
    let mut is_absolute = false;

    for (i, seg) in target_segments.iter().enumerate() {
        if *seg == "crate" {
            if i == 0 {
                resolved_segments.clear();
                is_absolute = true;
            } else {
                return Err("Path segment 'crate' must be at the beginning".to_string());
            }
        } else if *seg == "super" {
            if resolved_segments.is_empty() {
                return Err("Cannot use 'super' on the root module".to_string());
            }
            resolved_segments.pop();
        } else {
            resolved_segments.push(seg.to_string());
        }
    }

    let fq_candidate = resolved_segments.join("::");

    if let Some(pos) = library.names.iter().position(|n| n == &fq_candidate) {
        return Ok(SentenceIndex::from(pos));
    }

    // Fallback: Try absolute/as-is if not already parsed as absolute
    if !is_absolute {
        if let Some(pos) = library.names.iter().position(|n| n == safety_fn_name) {
            return Ok(SentenceIndex::from(pos));
        }
    }

    Err(format!(
        "Safety function '{}' not found in library",
        safety_fn_name
    ))
}

fn check_recursive_annotations(library: &Library) -> Result<(), String> {
    for s_idx_raw in 0..library.sentences.len() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        let has_annotation = library.annotations[s_idx].iter().any(|ann| matches!(ann, Annotation::Recursive));
        
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();
        let reachable_cycle = has_cycle(s_idx, library, &mut visited, &mut rec_stack);
        
        if reachable_cycle && !has_annotation {
            return Err(format!(
                "Sentence '{}' is recursive or calls a recursive sentence but is not annotated with #[recursive]",
                get_sentence_name(s_idx, library)
            ));
        }
    }
    Ok(())
}

pub fn check_precondition(library: &Library) -> Result<(), String> {
    // 0. Verify that all recursive sentences in the library are correctly annotated with #[recursive]
    check_recursive_annotations(library)?;

    // 1. Collect precondition, postcondition, and total checks
    let mut precondition_checks = Vec::new();
    let mut postcondition_checks = Vec::new();
    let mut total_checks = Vec::new();
    for (s_idx_raw, annotations) in library.annotations.iter().enumerate() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        let is_recursive = annotations.iter().any(|ann| matches!(ann, Annotation::Recursive));
        let mut precondition_fn = None;
        let mut postcondition_fn = None;
        let mut has_total = false;
        for ann in annotations {
            match ann {
                Annotation::Precondition(s_fn) => precondition_fn = Some(s_fn.clone()),
                Annotation::Postcondition(s_fn) => postcondition_fn = Some(s_fn.clone()),
                Annotation::Total => has_total = true,
                _ => {}
            }
        }

        let mut pre_idx_opt = None;
        if let Some(s_fn) = precondition_fn {
            let annotated_name = &library.names[s_idx];
            let safety_fn_idx = resolve_safety_fn(annotated_name, &s_fn, library)?;
            let safety_is_recursive = library.annotations[safety_fn_idx].iter().any(|ann| matches!(ann, Annotation::Recursive));
            
            if is_recursive || safety_is_recursive {
                println!(
                    "Skipping precondition check for '{}' (precondition '{}') because it is marked as recursive.",
                    get_sentence_name(s_idx, library),
                    get_sentence_name(safety_fn_idx, library)
                );
            } else {
                precondition_checks.push((s_idx, safety_fn_idx));
                pre_idx_opt = Some(safety_fn_idx);
            }
        }

        if let Some(s_fn) = postcondition_fn {
            let annotated_name = &library.names[s_idx];
            let post_fn_idx = resolve_safety_fn(annotated_name, &s_fn, library)?;
            let post_is_recursive = library.annotations[post_fn_idx].iter().any(|ann| matches!(ann, Annotation::Recursive));
            
            if is_recursive || post_is_recursive {
                println!(
                    "Skipping postcondition check for '{}' (postcondition '{}') because it is marked as recursive.",
                    get_sentence_name(s_idx, library),
                    get_sentence_name(post_fn_idx, library)
                );
            } else {
                postcondition_checks.push((s_idx, pre_idx_opt, post_fn_idx));
            }
        }

        if has_total {
            if is_recursive {
                println!(
                    "Skipping total check for '{}' because it is marked as recursive.",
                    get_sentence_name(s_idx, library)
                );
            } else {
                total_checks.push(s_idx);
            }
        }
    }

    if precondition_checks.is_empty() && postcondition_checks.is_empty() && total_checks.is_empty() {
        println!("No precondition, postcondition, or total annotations found.");
        return Ok(());
    }

    // 2. Collect all non-recursive sentences in the library to translate
    let mut ordered_sentences = Vec::new();
    for s_idx_raw in 0..library.sentences.len() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        let is_rec = library.annotations[s_idx].iter().any(|ann| matches!(ann, Annotation::Recursive));
        if !is_rec {
            ordered_sentences.push(s_idx);
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

    let mut symbol_ids = HashMap::new();
    for (id, name) in &symbols_list {
        symbol_ids.insert(name.clone(), *id);
    }

    // 6. Compute arity map by simulating the stack
    let mut arity_map = HashMap::new();
    let mut in_progress = HashSet::new();
    for &s_idx in &ordered_sentences {
        get_sentence_arity(s_idx, library, &mut arity_map, &mut in_progress)?;
    }

    // 7. Validate precondition arities
    for &(annotated_idx, safety_idx) in &precondition_checks {
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
                "Annotated function '{}' must have at least 1 output to be verified via typecheck",
                annotated_name
            ));
        }
    }

    // Validate postcondition arities
    for &(annotated_idx, pre_idx_opt, post_idx) in &postcondition_checks {
        let annotated_name = get_sentence_name(annotated_idx, library);
        let post_name = get_sentence_name(post_idx, library);

        let (n_post, m_post) = arity_map[&post_idx];
        let (n_annotated, m_annotated) = arity_map[&annotated_idx];

        if n_annotated != 1 || m_annotated != 1 {
            return Err(format!(
                "Annotated function '{}' must have arity 1 -> 1, but has {} -> {}",
                annotated_name, n_annotated, m_annotated
            ));
        }
        if n_post != 1 || m_post != 1 {
            return Err(format!(
                "Postcondition function '{}' must have arity 1 -> 1, but has {} -> {}",
                post_name, n_post, m_post
            ));
        }
        if let Some(pre_idx) = pre_idx_opt {
            let safety_name = get_sentence_name(pre_idx, library);
            let (n_safety, m_safety) = arity_map[&pre_idx];
            if n_safety != 1 || m_safety != 1 {
                return Err(format!(
                    "Safety function '{}' must have arity 1 -> 1, but has {} -> {}",
                    safety_name, n_safety, m_safety
                ));
            }
        }
    }

    // Validate total arities
    for &annotated_idx in &total_checks {
        let annotated_name = get_sentence_name(annotated_idx, library);
        let (n_annotated, m_annotated) = arity_map[&annotated_idx];
        if n_annotated != 1 {
            return Err(format!(
                "Annotated function '{}' must have 1 input, but has {}",
                annotated_name, n_annotated
            ));
        }
        if m_annotated == 0 {
            return Err(format!(
                "Annotated function '{}' must have at least 1 output to be verified via typecheck",
                annotated_name
            ));
        }
    }

    use z3::{Config, Solver, SatResult, Sort, RecFuncDecl, with_z3_config};
    use z3::{DatatypeBuilder, DatatypeAccessor};
    use z3::datatype_builder::create_datatypes;
    use z3::ast::{Ast, Bool, Int, Dynamic};

    let cfg = Config::new();
    let mut float_to_id = HashMap::new();

    with_z3_config(&cfg, || {
        // Build Datatype sorts programmatically
        let mut val_builder = DatatypeBuilder::new("Val")
            .variant("ValInt", vec![("getInt", DatatypeAccessor::sort(Sort::int()))])
            .variant("ValBool", vec![("getBool", DatatypeAccessor::sort(Sort::bool()))])
            .variant("ValFloat", vec![("getFloat", DatatypeAccessor::sort(Sort::int()))])
            .variant("ValSymbol", vec![("getSymbol", DatatypeAccessor::sort(Sort::int()))])
            .variant("ValTuple0", vec![]);

        let mut field_names_store = Vec::new();
        for &n in &tuple_sizes {
            if n == 0 { continue; }
            for i in 0..n {
                field_names_store.push(format!("getTuple{}_{}", n, i));
            }
        }

        let mut store_idx = 0;
        let mut val_tuple_variant_indices = Vec::new();
        for &n in &tuple_sizes {
            if n == 0 { continue; }
            let mut fields = Vec::new();
            for _ in 0..n {
                fields.push((field_names_store[store_idx].as_str(), DatatypeAccessor::datatype("Val")));
                store_idx += 1;
            }
            let variant_name = format!("ValTuple{}", n);
            val_builder = val_builder.variant(&variant_name, fields);
        }

        let result_builder = DatatypeBuilder::new("Result")
            .variant("Ok", vec![("getVal", DatatypeAccessor::datatype("Val"))])
            .variant("Panic", vec![]);

        let sorts = create_datatypes(vec![val_builder, result_builder]);
        let val_sort = &sorts[0].sort;
        let result_sort = &sorts[1].sort;

        let ok_con = &sorts[1].variants[0].constructor;
        let panic_val = sorts[1].variants[1].constructor.apply(&[]);

        // Store mappings for tuple variants
        let mut tuple_variants = HashMap::new();
        tuple_variants.insert(0, &sorts[0].variants[4]);
        
        let mut idx = 5;
        for &n in &tuple_sizes {
            if n == 0 { continue; }
            tuple_variants.insert(n, &sorts[0].variants[idx]);
            val_tuple_variant_indices.push((idx, n));
            idx += 1;
        }

        // Define Primitive RecFuncDecls
        let val_is_tuple_decl = RecFuncDecl::new("val_is_tuple", &[result_sort], result_sort);
        let val_tuple_length_decl = RecFuncDecl::new("val_tuple_length", &[result_sort], result_sort);
        let val_cond_decl = RecFuncDecl::new("val_cond", &[result_sort, result_sort, result_sort], result_sort);
        let val_is_true_decl = RecFuncDecl::new("val_is_true", &[result_sort], &Sort::bool());
        let val_equal_decl = RecFuncDecl::new("val_equal", &[result_sort, result_sort], result_sort);

        let val_add_decl = RecFuncDecl::new("val_add", &[result_sort, result_sort], result_sort);
        let val_sub_decl = RecFuncDecl::new("val_sub", &[result_sort, result_sort], result_sort);
        let val_mul_decl = RecFuncDecl::new("val_mul", &[result_sort, result_sort], result_sort);
        let val_div_decl = RecFuncDecl::new("val_div", &[result_sort, result_sort], result_sort);
        let val_mod_decl = RecFuncDecl::new("val_mod", &[result_sort, result_sort], result_sort);
        let val_neg_decl = RecFuncDecl::new("val_neg", &[result_sort], result_sort);
        let val_not_decl = RecFuncDecl::new("val_not", &[result_sort], result_sort);

        let val_less_decl = RecFuncDecl::new("val_less", &[result_sort, result_sort], result_sort);
        let val_greater_decl = RecFuncDecl::new("val_greater", &[result_sort, result_sort], result_sort);
        let val_and_decl = RecFuncDecl::new("val_and", &[result_sort, result_sort], result_sort);
        let val_or_decl = RecFuncDecl::new("val_or", &[result_sort, result_sort], result_sort);

        let val_is_int_decl = RecFuncDecl::new("val_is_int", &[result_sort], result_sort);
        let val_is_bool_decl = RecFuncDecl::new("val_is_bool", &[result_sort], result_sort);
        let val_is_symbol_decl = RecFuncDecl::new("val_is_symbol", &[result_sort], result_sort);
        let val_is_float_decl = RecFuncDecl::new("val_is_float", &[result_sort], result_sort);
        let val_is_numeric_decl = RecFuncDecl::new("val_is_numeric", &[result_sort], result_sort);

        let val_symbol_len_decl = RecFuncDecl::new("val_symbol_len", &[result_sort], result_sort);
        let val_symbol_char_at_decl = RecFuncDecl::new("val_symbol_char_at", &[result_sort, result_sort], result_sort);

        // Define bodies of Primitive RecFuncDecls
        {
            // 1. val_is_tuple
            let a = Dynamic::new_const("a", result_sort);
            let is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
            let get_val = sorts[1].variants[0].accessors[0].apply(&[&a]);

            let mut is_tuple_expr = sorts[0].variants[4].tester.apply(&[&get_val]).as_bool().unwrap();
            for &(variant_idx, _) in &val_tuple_variant_indices {
                let tester = &sorts[0].variants[variant_idx].tester;
                is_tuple_expr = Bool::or(&[&is_tuple_expr, &tester.apply(&[&get_val]).as_bool().unwrap()]);
            }
            let val_bool = sorts[0].variants[1].constructor.apply(&[&is_tuple_expr]);
            let ok_val_bool = sorts[1].variants[0].constructor.apply(&[&val_bool]);
            val_is_tuple_decl.add_def(&[&a], &is_ok.ite(&ok_val_bool, &panic_val));

            // 2. val_tuple_length
            let a = Dynamic::new_const("a", result_sort);
            let is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
            let is_tuple_res = val_is_tuple_decl.apply(&[&a]);
            let is_tuple_ok = sorts[1].variants[0].tester.apply(&[&is_tuple_res]).as_bool().unwrap();
            let is_tuple_val = sorts[1].variants[0].accessors[0].apply(&[&is_tuple_res]);
            let is_tuple_bool = sorts[0].variants[1].accessors[0].apply(&[&is_tuple_val]).as_bool().unwrap();
            let cond = Bool::and(&[&is_ok, &is_tuple_ok, &is_tuple_bool]);

            let get_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
            let mut length_expr = Int::from_i64(0);
            for &(variant_idx, n) in val_tuple_variant_indices.iter().rev() {
                let tester = &sorts[0].variants[variant_idx].tester;
                let is_n = tester.apply(&[&get_val]).as_bool().unwrap();
                length_expr = is_n.ite(&Int::from_i64(n as i64), &length_expr);
            }
            let val_int = sorts[0].variants[0].constructor.apply(&[&length_expr]);
            let ok_val_int = sorts[1].variants[0].constructor.apply(&[&val_int]);
            val_tuple_length_decl.add_def(&[&a], &cond.ite(&ok_val_int, &panic_val));

            // 3. val_cond
            let c = Dynamic::new_const("c", result_sort);
            let t = Dynamic::new_const("t", result_sort);
            let e = Dynamic::new_const("e", result_sort);
            let c_is_ok = sorts[1].variants[0].tester.apply(&[&c]).as_bool().unwrap();
            let c_val = sorts[1].variants[0].accessors[0].apply(&[&c]);
            let c_is_bool = sorts[0].variants[1].tester.apply(&[&c_val]).as_bool().unwrap();
            let cond = Bool::and(&[&c_is_ok, &c_is_bool]);
            let c_bool_val = sorts[0].variants[1].accessors[0].apply(&[&c_val]).as_bool().unwrap();
            val_cond_decl.add_def(&[&c, &t, &e], &cond.ite(&c_bool_val.ite(&t, &e), &panic_val));

            // 4. val_is_true
            let c = Dynamic::new_const("c", result_sort);
            let c_is_ok = sorts[1].variants[0].tester.apply(&[&c]).as_bool().unwrap();
            let c_val = sorts[1].variants[0].accessors[0].apply(&[&c]);
            let c_is_bool = sorts[0].variants[1].tester.apply(&[&c_val]).as_bool().unwrap();
            let c_bool_val = sorts[0].variants[1].accessors[0].apply(&[&c_val]).as_bool().unwrap();
            val_is_true_decl.add_def(&[&c], &Bool::and(&[&c_is_ok, &c_is_bool, &c_bool_val]));

            // 5. val_equal
            let a = Dynamic::new_const("a", result_sort);
            let b = Dynamic::new_const("b", result_sort);
            let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
            let b_is_ok = sorts[1].variants[0].tester.apply(&[&b]).as_bool().unwrap();
            let cond = Bool::and(&[&a_is_ok, &b_is_ok]);
            let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
            let b_val = sorts[1].variants[0].accessors[0].apply(&[&b]);
            let val_bool = sorts[0].variants[1].constructor.apply(&[&a_val.eq(&b_val)]);
            let ok_val_bool = sorts[1].variants[0].constructor.apply(&[&val_bool]);
            val_equal_decl.add_def(&[&a, &b], &cond.ite(&ok_val_bool, &panic_val));

            // Helper macro-like function to construct binary arithmetic/logical definitions
            let define_binary = |decl: &RecFuncDecl, make_op: fn(&Int, &Int) -> Int| {
                let a = Dynamic::new_const("a", result_sort);
                let b = Dynamic::new_const("b", result_sort);
                let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
                let b_is_ok = sorts[1].variants[0].tester.apply(&[&b]).as_bool().unwrap();
                let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
                let b_val = sorts[1].variants[0].accessors[0].apply(&[&b]);
                let a_is_int = sorts[0].variants[0].tester.apply(&[&a_val]).as_bool().unwrap();
                let b_is_int = sorts[0].variants[0].tester.apply(&[&b_val]).as_bool().unwrap();
                let cond = Bool::and(&[&a_is_ok, &b_is_ok, &a_is_int, &b_is_int]);
                let a_int = sorts[0].variants[0].accessors[0].apply(&[&a_val]).as_int().unwrap();
                let b_int = sorts[0].variants[0].accessors[0].apply(&[&b_val]).as_int().unwrap();
                let val_int = sorts[0].variants[0].constructor.apply(&[&make_op(&a_int, &b_int)]);
                let ok_val_int = sorts[1].variants[0].constructor.apply(&[&val_int]);
                decl.add_def(&[&a, &b], &cond.ite(&ok_val_int, &panic_val));
            };

            define_binary(&val_add_decl, |x, y| Int::add(&[x, y]));
            define_binary(&val_sub_decl, |x, y| Int::sub(&[x, y]));
            define_binary(&val_mul_decl, |x, y| Int::mul(&[x, y]));
            define_binary(&val_div_decl, |x, y| x.div(y));
            define_binary(&val_mod_decl, |x, y| x.modulo(y));

            // val_neg
            let a = Dynamic::new_const("a", result_sort);
            let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
            let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
            let a_is_int = sorts[0].variants[0].tester.apply(&[&a_val]).as_bool().unwrap();
            let cond = Bool::and(&[&a_is_ok, &a_is_int]);
            let a_int = sorts[0].variants[0].accessors[0].apply(&[&a_val]).as_int().unwrap();
            let val_int = sorts[0].variants[0].constructor.apply(&[&a_int.unary_minus()]);
            let ok_val_int = sorts[1].variants[0].constructor.apply(&[&val_int]);
            val_neg_decl.add_def(&[&a], &cond.ite(&ok_val_int, &panic_val));

            // val_not
            let a = Dynamic::new_const("a", result_sort);
            let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
            let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
            let a_is_bool = sorts[0].variants[1].tester.apply(&[&a_val]).as_bool().unwrap();
            let cond = Bool::and(&[&a_is_ok, &a_is_bool]);
            let a_bool = sorts[0].variants[1].accessors[0].apply(&[&a_val]).as_bool().unwrap();
            let val_bool = sorts[0].variants[1].constructor.apply(&[&a_bool.not()]);
            let ok_val_bool = sorts[1].variants[0].constructor.apply(&[&val_bool]);
            val_not_decl.add_def(&[&a], &cond.ite(&ok_val_bool, &panic_val));

            // Helper for binary boolean relations
            let define_binary_rel = |decl: &RecFuncDecl, make_op: fn(&Int, &Int) -> Bool| {
                let a = Dynamic::new_const("a", result_sort);
                let b = Dynamic::new_const("b", result_sort);
                let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
                let b_is_ok = sorts[1].variants[0].tester.apply(&[&b]).as_bool().unwrap();
                let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
                let b_val = sorts[1].variants[0].accessors[0].apply(&[&b]);
                let a_is_int = sorts[0].variants[0].tester.apply(&[&a_val]).as_bool().unwrap();
                let b_is_int = sorts[0].variants[0].tester.apply(&[&b_val]).as_bool().unwrap();
                let cond = Bool::and(&[&a_is_ok, &b_is_ok, &a_is_int, &b_is_int]);
                let a_int = sorts[0].variants[0].accessors[0].apply(&[&a_val]).as_int().unwrap();
                let b_int = sorts[0].variants[0].accessors[0].apply(&[&b_val]).as_int().unwrap();
                let val_bool = sorts[0].variants[1].constructor.apply(&[&make_op(&a_int, &b_int)]);
                let ok_val_bool = sorts[1].variants[0].constructor.apply(&[&val_bool]);
                decl.add_def(&[&a, &b], &cond.ite(&ok_val_bool, &panic_val));
            };

            define_binary_rel(&val_less_decl, |x, y| x.lt(y));
            define_binary_rel(&val_greater_decl, |x, y| x.gt(y));

            // val_and, val_or
            let define_binary_logical = |decl: &RecFuncDecl, make_op: fn(&Bool, &Bool) -> Bool| {
                let a = Dynamic::new_const("a", result_sort);
                let b = Dynamic::new_const("b", result_sort);
                let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
                let b_is_ok = sorts[1].variants[0].tester.apply(&[&b]).as_bool().unwrap();
                let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
                let b_val = sorts[1].variants[0].accessors[0].apply(&[&b]);
                let a_is_bool = sorts[0].variants[1].tester.apply(&[&a_val]).as_bool().unwrap();
                let b_is_bool = sorts[0].variants[1].tester.apply(&[&b_val]).as_bool().unwrap();
                let cond = Bool::and(&[&a_is_ok, &b_is_ok, &a_is_bool, &b_is_bool]);
                let a_bool = sorts[0].variants[1].accessors[0].apply(&[&a_val]).as_bool().unwrap();
                let b_bool = sorts[0].variants[1].accessors[0].apply(&[&b_val]).as_bool().unwrap();
                let val_bool = sorts[0].variants[1].constructor.apply(&[&make_op(&a_bool, &b_bool)]);
                let ok_val_bool = sorts[1].variants[0].constructor.apply(&[&val_bool]);
                decl.add_def(&[&a, &b], &cond.ite(&ok_val_bool, &panic_val));
            };

            define_binary_logical(&val_and_decl, |x, y| Bool::and(&[x, y]));
            define_binary_logical(&val_or_decl, |x, y| Bool::or(&[x, y]));

            // Type testers
            let define_tester = |decl: &RecFuncDecl, variant_idx: usize| {
                let a = Dynamic::new_const("a", result_sort);
                let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
                let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
                let tester = &sorts[0].variants[variant_idx].tester;
                let is_type = tester.apply(&[&a_val]).as_bool().unwrap();
                let val_bool = sorts[0].variants[1].constructor.apply(&[&is_type]);
                let ok_val_bool = sorts[1].variants[0].constructor.apply(&[&val_bool]);
                decl.add_def(&[&a], &a_is_ok.ite(&ok_val_bool, &panic_val));
            };

            define_tester(&val_is_int_decl, 0);
            define_tester(&val_is_bool_decl, 1);
            define_tester(&val_is_symbol_decl, 3);
            define_tester(&val_is_float_decl, 2);

            // val_is_numeric
            {
                let a = Dynamic::new_const("a", result_sort);
                let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
                let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
                let a_is_int = sorts[0].variants[0].tester.apply(&[&a_val]).as_bool().unwrap();
                let a_is_float = sorts[0].variants[2].tester.apply(&[&a_val]).as_bool().unwrap();
                let is_num = Bool::or(&[&a_is_int, &a_is_float]);
                let val_bool = sorts[0].variants[1].constructor.apply(&[&is_num]);
                let ok_val_bool = sorts[1].variants[0].constructor.apply(&[&val_bool]);
                val_is_numeric_decl.add_def(&[&a], &a_is_ok.ite(&ok_val_bool, &panic_val));
            }

            // Static symbol length & char_at handlers
            {
                // val_symbol_len
                let a = Dynamic::new_const("a", result_sort);
                let a_is_ok = sorts[1].variants[0].tester.apply(&[&a]).as_bool().unwrap();
                let a_val = sorts[1].variants[0].accessors[0].apply(&[&a]);
                let a_is_sym = sorts[0].variants[3].tester.apply(&[&a_val]).as_bool().unwrap();
                let cond = Bool::and(&[&a_is_ok, &a_is_sym]);

                let sym_id = sorts[0].variants[3].accessors[0].apply(&[&a_val]).as_int().unwrap();
                let mut len_expr = Int::from_i64(0);
                for &(id, ref name) in &symbols_list {
                    let is_id = sym_id.eq(&Int::from_i64(id as i64));
                    len_expr = is_id.ite(&Int::from_i64(name.len() as i64), &len_expr);
                }
                let val_int = sorts[0].variants[0].constructor.apply(&[&len_expr]);
                let ok_val_int = sorts[1].variants[0].constructor.apply(&[&val_int]);
                val_symbol_len_decl.add_def(&[&a], &cond.ite(&ok_val_int, &panic_val));

                // val_symbol_char_at
                let sym = Dynamic::new_const("sym", result_sort);
                let idx = Dynamic::new_const("idx", result_sort);
                let sym_is_ok = sorts[1].variants[0].tester.apply(&[&sym]).as_bool().unwrap();
                let idx_is_ok = sorts[1].variants[0].tester.apply(&[&idx]).as_bool().unwrap();
                let sym_val = sorts[1].variants[0].accessors[0].apply(&[&sym]);
                let idx_val = sorts[1].variants[0].accessors[0].apply(&[&idx]);
                let sym_is_sym = sorts[0].variants[3].tester.apply(&[&sym_val]).as_bool().unwrap();
                let idx_is_int = sorts[0].variants[0].tester.apply(&[&idx_val]).as_bool().unwrap();
                let cond = Bool::and(&[&sym_is_ok, &idx_is_ok, &sym_is_sym, &idx_is_int]);

                let sym_id = sorts[0].variants[3].accessors[0].apply(&[&sym_val]).as_int().unwrap();
                let idx_int = sorts[0].variants[0].accessors[0].apply(&[&idx_val]).as_int().unwrap();
                let mut char_code_expr = Int::from_i64(-1);
                for &(id, ref name) in &symbols_list {
                    let is_id = sym_id.eq(&Int::from_i64(id as i64));
                    let mut inner_expr = Int::from_i64(-1);
                    for j in 0..name.len() {
                        let is_j = idx_int.eq(&Int::from_i64(j as i64));
                        let char_code = name.as_bytes()[j] as i64;
                        inner_expr = is_j.ite(&Int::from_i64(char_code), &inner_expr);
                    }
                    char_code_expr = is_id.ite(&inner_expr, &char_code_expr);
                }
                
                // Panic if idx is out of bounds or negative
                let char_ok_cond = char_code_expr.ge(&Int::from_i64(0));
                let final_cond = Bool::and(&[&cond, &char_ok_cond]);
                
                let val_int = sorts[0].variants[0].constructor.apply(&[&char_code_expr]);
                let ok_val_int = sorts[1].variants[0].constructor.apply(&[&val_int]);
                val_symbol_char_at_decl.add_def(&[&sym, &idx], &final_cond.ite(&ok_val_int, &panic_val));
            }
        }

        let mut val_tuple_decls = HashMap::new();
        let mut val_get_tuple_decls = HashMap::new();

        for &n in &tuple_sizes {
            if n == 0 { continue; }
            
            // val_tuple{n}
            let tuple_domain = vec![result_sort; n];
            let val_tuple_decl = RecFuncDecl::new(format!("val_tuple{}", n), &tuple_domain, result_sort);
            
            let mut inputs = Vec::new();
            for i in 0..n {
                inputs.push(Dynamic::new_const(format!("e{}", i), result_sort));
            }
            let inputs_refs: Vec<&dyn Ast> = inputs.iter().map(|v| v as &dyn Ast).collect();

            let mut is_ok_cond = Bool::from_bool(true);
            let mut val_args = Vec::new();
            for i in 0..n {
                let e = &inputs[i];
                let e_is_ok = sorts[1].variants[0].tester.apply(&[e]).as_bool().unwrap();
                is_ok_cond = Bool::and(&[&is_ok_cond, &e_is_ok]);
                let e_val = sorts[1].variants[0].accessors[0].apply(&[e]);
                val_args.push(e_val);
            }
            
            let val_args_refs: Vec<&dyn Ast> = val_args.iter().map(|v| v as &dyn Ast).collect();
            let variant = tuple_variants[&n];
            let tuple_val = variant.constructor.apply(&val_args_refs);
            let ok_tuple_val = sorts[1].variants[0].constructor.apply(&[&tuple_val]);
            
            val_tuple_decl.add_def(&inputs_refs, &is_ok_cond.ite(&ok_tuple_val, &panic_val));
            val_tuple_decls.insert(n, val_tuple_decl);

            // val_getTuple{n}_{i}
            for i in 0..n {
                let val_get_tuple_decl = RecFuncDecl::new(format!("val_getTuple{}_{}", n, i), &[result_sort], result_sort);
                let t = Dynamic::new_const("t", result_sort);
                
                let t_is_ok = sorts[1].variants[0].tester.apply(&[&t]).as_bool().unwrap();
                let t_val = sorts[1].variants[0].accessors[0].apply(&[&t]);
                let t_is_tuple = variant.tester.apply(&[&t_val]).as_bool().unwrap();
                let cond = Bool::and(&[&t_is_ok, &t_is_tuple]);

                let field_val = variant.accessors[i].apply(&[&t_val]);
                let ok_field_val = sorts[1].variants[0].constructor.apply(&[&field_val]);
                
                val_get_tuple_decl.add_def(&[&t], &cond.ite(&ok_field_val, &panic_val));
                val_get_tuple_decls.insert((n, i), val_get_tuple_decl);
            }
        }

        // Pass 1: Declare all target/dependency sentences
        let mut sentence_decls = HashMap::new();
        for &s_idx in &ordered_sentences {
            let name = get_sentence_name(s_idx, library);
            let (n_inputs, n_outputs) = arity_map[&s_idx];
            
            let mut decls = Vec::new();
            for i in 0..n_outputs {
                let decl_name = format!("{}_out_{}", name, i);
                let domain = vec![result_sort; n_inputs];
                let decl = RecFuncDecl::new(decl_name, &domain, result_sort);
                decls.push(decl);
            }
            sentence_decls.insert(s_idx, decls);
        }

        // Pass 2: Define all sentence bodies
        for &s_idx in &ordered_sentences {
            let (n_inputs, n_outputs) = arity_map[&s_idx];
            let sentence = &library.sentences[s_idx];

            let mut args = Vec::new();
            for i in 0..n_inputs {
                args.push(Dynamic::new_const(format!("in_{}", i), result_sort));
            }
            let args_refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();

            let mut stack = args.clone();
            let mut ok = Bool::from_bool(true);

            for inst in sentence {
                match inst {
                    Instruction::Push(val) => {
                        let res = match val {
                            Value::Int(v) => {
                                let int_val = sorts[0].variants[0].constructor.apply(&[&Int::from_i64(*v)]);
                                sorts[1].variants[0].constructor.apply(&[&int_val])
                            }
                            Value::Bool(b) => {
                                let bool_val = sorts[0].variants[1].constructor.apply(&[&Bool::from_bool(*b)]);
                                sorts[1].variants[0].constructor.apply(&[&bool_val])
                            }
                            Value::Float(f) => {
                                let next_id = float_to_id.len();
                                let f_id = *float_to_id.entry(f.to_string()).or_insert(next_id);
                                let float_val = sorts[0].variants[2].constructor.apply(&[&Int::from_i64(f_id as i64)]);
                                sorts[1].variants[0].constructor.apply(&[&float_val])
                            }
                            Value::Symbol(s) => {
                                let s_id = symbol_ids[&s.name];
                                let sym_val = sorts[0].variants[3].constructor.apply(&[&Int::from_i64(s_id as i64)]);
                                sorts[1].variants[0].constructor.apply(&[&sym_val])
                            }
                            Value::Tuple(_) => {
                                fn construct_tuple_val(
                                    val: &Value,
                                    sorts: &[z3::DatatypeSort],
                                    tuple_variants: &HashMap<usize, &z3::DatatypeVariant>,
                                    float_to_id: &mut HashMap<String, usize>,
                                    symbol_ids: &HashMap<String, usize>,
                                ) -> Dynamic {
                                    match val {
                                        Value::Int(v) => sorts[0].variants[0].constructor.apply(&[&Int::from_i64(*v)]),
                                        Value::Bool(b) => sorts[0].variants[1].constructor.apply(&[&Bool::from_bool(*b)]),
                                        Value::Float(f) => {
                                            let next_id = float_to_id.len();
                                            let f_id = *float_to_id.entry(f.to_string()).or_insert(next_id);
                                            sorts[0].variants[2].constructor.apply(&[&Int::from_i64(f_id as i64)])
                                        }
                                        Value::Symbol(s) => {
                                            let s_id = symbol_ids[&s.name];
                                            sorts[0].variants[3].constructor.apply(&[&Int::from_i64(s_id as i64)])
                                        }
                                        Value::Tuple(elements) => {
                                            let mut args = Vec::new();
                                            for elem in elements {
                                                args.push(construct_tuple_val(elem, sorts, tuple_variants, float_to_id, symbol_ids));
                                            }
                                            let args_refs: Vec<&dyn Ast> = args.iter().map(|v| v as &dyn Ast).collect();
                                            let variant = tuple_variants[&elements.len()];
                                            variant.constructor.apply(&args_refs)
                                        }
                                    }
                                }
                                let tuple_val = construct_tuple_val(val, &sorts, &tuple_variants, &mut float_to_id, &symbol_ids);
                                sorts[1].variants[0].constructor.apply(&[&tuple_val])
                            }
                        };
                        stack.push(res);
                    }
                    Instruction::Drop(n) => {
                        stack.remove(stack.len() - 1 - n);
                    }
                    Instruction::Pick(n) => {
                        stack.push(stack[stack.len() - 1 - n].clone());
                    }
                    Instruction::Roll(n) => {
                        let val = stack.remove(stack.len() - 1 - n);
                        stack.push(val);
                    }
                    Instruction::Tuple(n) => {
                        let n = *n;
                        // Per the language spec (docs/hana_reference.md), `tuple N` pops N
                        // elements and the TOS element (popped first) becomes index 0 of the
                        // tuple, so the popped order is already the correct field order.
                        let mut tuple_args = Vec::new();
                        for _ in 0..n {
                            tuple_args.push(stack.pop().unwrap());
                        }

                        let tuple_res = if n == 0 {
                            let tuple_val = tuple_variants[&0].constructor.apply(&[]);
                            sorts[1].variants[0].constructor.apply(&[&tuple_val])
                        } else {
                            let args_refs: Vec<&dyn Ast> = tuple_args.iter().map(|v| v as &dyn Ast).collect();
                            val_tuple_decls[&n].apply(&args_refs)
                        };
                        stack.push(tuple_res);
                    }
                    Instruction::Untuple(n) => {
                        let n = *n;
                        let val = stack.pop().unwrap();
                        // Symmetric with `Tuple`: index 0 must end up on top of the stack, so
                        // fields are pushed in reverse index order (N-1 down to 0).
                        let mut unpacked = Vec::new();
                        for i in (0..n).rev() {
                            let get_fn = &val_get_tuple_decls[&(n, i)];
                            let component = get_fn.apply(&[&val]);
                            unpacked.push(component);
                        }
                        for component in &unpacked {
                            let comp_is_ok = sorts[1].variants[0].tester.apply(&[component]).as_bool().unwrap();
                            ok = Bool::and(&[&ok, &comp_is_ok]);
                        }
                        stack.extend(unpacked);
                    }
                    Instruction::Jump(target) => {
                        let (n_t, m_t) = arity_map[target];
                        let mut jump_args = Vec::new();
                        for _ in 0..n_t {
                            jump_args.push(stack.pop().unwrap());
                        }
                        jump_args.reverse();

                        let target_decls = &sentence_decls[target];
                        let mut results = Vec::new();
                        for i in 0..m_t {
                            let args_refs: Vec<&dyn Ast> = jump_args.iter().map(|v| v as &dyn Ast).collect();
                            results.push(target_decls[i].apply(&args_refs));
                        }
                        for res in &results {
                            let res_is_ok = sorts[1].variants[0].tester.apply(&[res]).as_bool().unwrap();
                            ok = Bool::and(&[&ok, &res_is_ok]);
                        }
                        stack.extend(results);
                    }
                    Instruction::Branch(then_t, else_t) => {
                        let cond_var = stack.pop().unwrap();
                        let (n_then, m_then) = arity_map[then_t];
                        let (n_else, m_else) = arity_map[else_t];
                        let max_n = std::cmp::max(n_then, n_else);
                        let max_m = std::cmp::max(m_then, m_else);

                        let mut branch_inputs = Vec::new();
                        for _ in 0..max_n {
                            branch_inputs.push(stack.pop().unwrap());
                        }
                        branch_inputs.reverse();

                        let mut then_args = Vec::new();
                        for i in (max_n - n_then)..max_n {
                            then_args.push(branch_inputs[i].clone());
                        }
                        let mut else_args = Vec::new();
                        for i in (max_n - n_else)..max_n {
                            else_args.push(branch_inputs[i].clone());
                        }

                        let cond_valid = val_is_bool_decl.apply(&[&cond_var]);
                        let cond_valid_bool = sorts[1].variants[0].tester.apply(&[&cond_valid]).as_bool().unwrap();
                        ok = Bool::and(&[&ok, &cond_valid_bool]);

                        let cond_is_true = val_is_true_decl.apply(&[&cond_var]).as_bool().unwrap();
                        let then_decls = &sentence_decls[then_t];
                        let else_decls = &sentence_decls[else_t];

                        let mut results = Vec::new();
                        for i in 0..max_m {
                            let then_args_refs: Vec<&dyn Ast> = then_args.iter().map(|v| v as &dyn Ast).collect();
                            let else_args_refs: Vec<&dyn Ast> = else_args.iter().map(|v| v as &dyn Ast).collect();
                            let then_expr = if i < then_decls.len() {
                                then_decls[i].apply(&then_args_refs)
                            } else {
                                panic_val.clone()
                            };
                            let else_expr = if i < else_decls.len() {
                                else_decls[i].apply(&else_args_refs)
                            } else {
                                panic_val.clone()
                            };
                            results.push(cond_is_true.ite(&then_expr, &else_expr));
                        }
                        for res in &results {
                            let res_is_ok = sorts[1].variants[0].tester.apply(&[res]).as_bool().unwrap();
                            ok = Bool::and(&[&ok, &res_is_ok]);
                        }
                        stack.extend(results);
                    }
                    Instruction::Add | Instruction::Subtract | Instruction::Multiply | Instruction::Divide | Instruction::Modulo |
                    Instruction::Equal | Instruction::Less | Instruction::Greater | Instruction::And | Instruction::Or => {
                        let b = stack.pop().unwrap();
                        let a = stack.pop().unwrap();
                        let res = match inst {
                            Instruction::Add => val_add_decl.apply(&[&a, &b]),
                            Instruction::Subtract => val_sub_decl.apply(&[&a, &b]),
                            Instruction::Multiply => val_mul_decl.apply(&[&a, &b]),
                            Instruction::Divide => val_div_decl.apply(&[&a, &b]),
                            Instruction::Modulo => val_mod_decl.apply(&[&a, &b]),
                            Instruction::Equal => val_equal_decl.apply(&[&a, &b]),
                            Instruction::Less => val_less_decl.apply(&[&a, &b]),
                            Instruction::Greater => val_greater_decl.apply(&[&a, &b]),
                            Instruction::And => val_and_decl.apply(&[&a, &b]),
                            Instruction::Or => val_or_decl.apply(&[&a, &b]),
                            _ => unreachable!(),
                        };
                        let res_is_ok = sorts[1].variants[0].tester.apply(&[&res]).as_bool().unwrap();
                        ok = Bool::and(&[&ok, &res_is_ok]);
                        stack.push(res);
                    }
                    Instruction::Negate | Instruction::Not | Instruction::IsInt | Instruction::IsBool |
                    Instruction::IsSymbol | Instruction::IsFloat | Instruction::IsTuple |
                    Instruction::TupleLength | Instruction::SymbolLen | Instruction::SymbolCharAt => {
                        let res = match inst {
                            Instruction::SymbolCharAt => {
                                let idx = stack.pop().unwrap();
                                let sym = stack.pop().unwrap();
                                val_symbol_char_at_decl.apply(&[&sym, &idx])
                            }
                            _ => {
                                let a = stack.pop().unwrap();
                                match inst {
                                    Instruction::Negate => val_neg_decl.apply(&[&a]),
                                    Instruction::Not => val_not_decl.apply(&[&a]),
                                    Instruction::IsInt => val_is_int_decl.apply(&[&a]),
                                    Instruction::IsBool => val_is_bool_decl.apply(&[&a]),
                                    Instruction::IsSymbol => val_is_symbol_decl.apply(&[&a]),
                                    Instruction::IsFloat => val_is_float_decl.apply(&[&a]),
                                    Instruction::IsTuple => val_is_tuple_decl.apply(&[&a]),
                                    Instruction::TupleLength => val_tuple_length_decl.apply(&[&a]),
                                    Instruction::SymbolLen => val_symbol_len_decl.apply(&[&a]),
                                    _ => unreachable!(),
                                }
                            }
                        };
                        let res_is_ok = sorts[1].variants[0].tester.apply(&[&res]).as_bool().unwrap();
                        ok = Bool::and(&[&ok, &res_is_ok]);
                        stack.push(res);
                    }
                    Instruction::Panic => {
                        ok = Bool::from_bool(false);
                    }
                    Instruction::Assert => {
                        let cond_var = stack.pop().unwrap();
                        let cond_is_true = val_is_true_decl.apply(&[&cond_var]).as_bool().unwrap();
                        ok = Bool::and(&[&ok, &cond_is_true]);
                    }
                    Instruction::AssertEqual => {
                        let b = stack.pop().unwrap();
                        let a = stack.pop().unwrap();
                        let eq_res = val_equal_decl.apply(&[&a, &b]);
                        let eq_is_true = val_is_true_decl.apply(&[&eq_res]).as_bool().unwrap();
                        ok = Bool::and(&[&ok, &eq_is_true]);
                    }
                    Instruction::Print => {
                        stack.pop();
                    }
                }
            }

            // Define each output function body
            let decls = &sentence_decls[&s_idx];
            for i in 0..n_outputs {
                let final_expr = &stack[stack.len() - 1 - i];
                let body = ok.ite(final_expr, &panic_val);
                decls[i].add_def(&args_refs, &body);
            }
        }

        // Build reverse lookup tables so counterexamples can be rendered with real
        // symbol names and tuple field order instead of raw Z3 datatype terms.
        let symbol_names: HashMap<i64, String> = symbols_list
            .iter()
            .map(|(id, name)| (*id as i64, name.clone()))
            .collect();
        let float_values: HashMap<i64, String> = float_to_id
            .iter()
            .map(|(s, id)| (*id as i64, s.clone()))
            .collect();
        let mut tuple_arities: HashMap<usize, usize> = HashMap::new();
        tuple_arities.insert(4, 0);
        for &(variant_idx, n) in &val_tuple_variant_indices {
            tuple_arities.insert(variant_idx, n);
        }

        // Recursively decode a model value for the `Val` datatype into a
        // human-readable string matching `Value`'s Display format (correct tuple
        // field order, symbols resolved by name instead of raw id).
        fn format_model_val(
            val: &Dynamic,
            model: &z3::Model,
            sorts: &[z3::DatatypeSort],
            tuple_arities: &HashMap<usize, usize>,
            symbol_names: &HashMap<i64, String>,
            float_values: &HashMap<i64, String>,
        ) -> String {
            for (variant_idx, variant) in sorts[0].variants.iter().enumerate() {
                let tester_bool = variant.tester.apply(&[val]).as_bool().unwrap();
                let matches = model
                    .eval(&tester_bool, true)
                    .and_then(|b| b.as_bool())
                    .unwrap_or(false);
                if !matches {
                    continue;
                }

                return match variant_idx {
                    0 => {
                        let field = model.eval(&variant.accessors[0].apply(&[val]), true).unwrap();
                        field.as_int().unwrap().as_i64().unwrap().to_string()
                    }
                    1 => {
                        let field = model.eval(&variant.accessors[0].apply(&[val]), true).unwrap();
                        field.as_bool().unwrap().as_bool().unwrap().to_string()
                    }
                    2 => {
                        let field = model.eval(&variant.accessors[0].apply(&[val]), true).unwrap();
                        let id = field.as_int().unwrap().as_i64().unwrap();
                        float_values
                            .get(&id)
                            .cloned()
                            .unwrap_or_else(|| format!("<float#{}>", id))
                    }
                    3 => {
                        let field = model.eval(&variant.accessors[0].apply(&[val]), true).unwrap();
                        let id = field.as_int().unwrap().as_i64().unwrap();
                        let name = symbol_names
                            .get(&id)
                            .cloned()
                            .unwrap_or_else(|| format!("#{}", id));
                        format!("symbol({})", name)
                    }
                    _ => {
                        let n = tuple_arities.get(&variant_idx).copied().unwrap_or(0);
                        let mut parts = Vec::with_capacity(n);
                        for k in 0..n {
                            let field = model.eval(&variant.accessors[k].apply(&[val]), true).unwrap();
                            parts.push(format_model_val(
                                &field,
                                model,
                                sorts,
                                tuple_arities,
                                symbol_names,
                                float_values,
                            ));
                        }
                        let mut s = format!("({}", parts.join(", "));
                        if n == 1 {
                            s.push(',');
                        }
                        s.push(')');
                        s
                    }
                };
            }

            "<unknown>".to_string()
        }

        // 8. Solve precondition verification checks programmatically
        let mut failed_checks = Vec::new();

        for (annotated_idx, safety_idx) in precondition_checks {
            let annotated_name = get_sentence_name(annotated_idx, library);
            let safety_name = get_sentence_name(safety_idx, library);

            let solver = Solver::new();

            // Build programmatic precondition check logic
            let x = Dynamic::new_const("x", val_sort);
            
            // ok_x = Ok(x)
            let ok_x = ok_con.apply(&[&x]);

            // safety_app = safety_decl[0].apply(&[ok_x])
            let safety_decl = &sentence_decls[&safety_idx][0];
            let safety_app = safety_decl.apply(&[&ok_x]);

            // True Result value: Ok(ValBool(true))
            let val_bool_con = &sorts[0].variants[1].constructor;
            let val_bool_true = val_bool_con.apply(&[&Bool::from_bool(true)]);
            let ok_val_bool_true = ok_con.apply(&[&val_bool_true]);

            // Assert safety_app == Ok(ValBool(true))
            solver.assert(&safety_app.eq(&ok_val_bool_true));

            // annotated_app = annotated_decl[0].apply(&[ok_x])
            let annotated_decl = &sentence_decls[&annotated_idx][0];
            let annotated_app = annotated_decl.apply(&[&ok_x]);

            // Assert is_panic(annotated_app)
            let is_panic_tester = &sorts[1].variants[1].tester;
            let is_panic_bool = is_panic_tester.apply(&[&annotated_app]).as_bool().unwrap();
            solver.assert(&is_panic_bool);

            match solver.check() {
                SatResult::Unsat => {
                    println!(
                        "[PASS] '{}' never panics when '{}' returns true",
                        annotated_name, safety_name
                    );
                }
                SatResult::Sat => {
                    let mut error_msg = format!(
                        "'{}' can panic when '{}' returns true",
                        annotated_name, safety_name
                    );
                    let mut counterexample = String::new();
                    if let Some(model) = solver.get_model() {
                        if let Some(val) = model.eval(&x, true) {
                            let rendered = format_model_val(
                                &val,
                                &model,
                                &sorts,
                                &tuple_arities,
                                &symbol_names,
                                &float_values,
                            );
                            counterexample = format!(" (Counterexample: x = {})", rendered);
                        }
                    }
                    error_msg.push_str(&counterexample);
                    failed_checks.push(error_msg);
                    println!(
                        "[FAIL] '{}' can panic when '{}' returns true!{}",
                        annotated_name, safety_name, counterexample
                    );
                }
                SatResult::Unknown => {
                    return Err(format!(
                        "Z3 solver returned Unknown for precondition check between '{}' and '{}'",
                        annotated_name, safety_name
                    ));
                }
            }
        }

        // 9. Solve postcondition verification checks programmatically
        for (annotated_idx, pre_idx_opt, post_idx) in postcondition_checks {
            let annotated_name = get_sentence_name(annotated_idx, library);
            let post_name = get_sentence_name(post_idx, library);

            let solver = Solver::new();

            // Build programmatic postcondition check logic
            let x = Dynamic::new_const("x", val_sort);
            
            // ok_x = Ok(x)
            let ok_x = ok_con.apply(&[&x]);

            // If there's a precondition P, assert P(Ok(x)) == Ok(ValBool(true))
            if let Some(pre_idx) = pre_idx_opt {
                let safety_decl = &sentence_decls[&pre_idx][0];
                let safety_app = safety_decl.apply(&[&ok_x]);

                let val_bool_con = &sorts[0].variants[1].constructor;
                let val_bool_true = val_bool_con.apply(&[&Bool::from_bool(true)]);
                let ok_val_bool_true = ok_con.apply(&[&val_bool_true]);

                solver.assert(&safety_app.eq(&ok_val_bool_true));
            }

            // Apply annotated function F to get output: y = F_out_0(ok_x)
            let annotated_decl = &sentence_decls[&annotated_idx][0];
            let y = annotated_decl.apply(&[&ok_x]);

            // Apply postcondition function Q to output: Q_out_0(y)
            let post_decl = &sentence_decls[&post_idx][0];
            let post_app = post_decl.apply(&[&y]);

            // True Result value: Ok(ValBool(true))
            let val_bool_con = &sorts[0].variants[1].constructor;
            let val_bool_true = val_bool_con.apply(&[&Bool::from_bool(true)]);
            let ok_val_bool_true = ok_con.apply(&[&val_bool_true]);

            // We assert post_app != Ok(ValBool(true)) to find a counterexample.
            solver.assert(&post_app.eq(&ok_val_bool_true).not());

            match solver.check() {
                SatResult::Unsat => {
                    if let Some(pre_idx) = pre_idx_opt {
                        let safety_name = get_sentence_name(pre_idx, library);
                        println!(
                            "[PASS] '{}' postcondition '{}' holds when precondition '{}' returns true",
                            annotated_name, post_name, safety_name
                        );
                    } else {
                        println!(
                            "[PASS] '{}' postcondition '{}' holds",
                            annotated_name, post_name
                        );
                    }
                }
                SatResult::Sat => {
                    let mut error_msg = if let Some(pre_idx) = pre_idx_opt {
                        let safety_name = get_sentence_name(pre_idx, library);
                        format!(
                            "'{}' postcondition '{}' can fail when precondition '{}' returns true",
                            annotated_name, post_name, safety_name
                        )
                    } else {
                        format!(
                            "'{}' postcondition '{}' can fail",
                            annotated_name, post_name
                        )
                    };
                    let mut counterexample = String::new();
                    if let Some(model) = solver.get_model() {
                        if let Some(val) = model.eval(&x, true) {
                            let rendered = format_model_val(
                                &val,
                                &model,
                                &sorts,
                                &tuple_arities,
                                &symbol_names,
                                &float_values,
                            );
                            counterexample = format!(" (Counterexample: x = {})", rendered);
                        }
                    }
                    error_msg.push_str(&counterexample);
                    failed_checks.push(error_msg);
                    if let Some(pre_idx) = pre_idx_opt {
                        let safety_name = get_sentence_name(pre_idx, library);
                        println!(
                            "[FAIL] '{}' postcondition '{}' can fail when precondition '{}' returns true!{}",
                            annotated_name, post_name, safety_name, counterexample
                        );
                    } else {
                        println!(
                            "[FAIL] '{}' postcondition '{}' can fail!{}",
                            annotated_name, post_name, counterexample
                        );
                    }
                }
                SatResult::Unknown => {
                    return Err(format!(
                        "Z3 solver returned Unknown for postcondition check between '{}' and '{}'",
                        annotated_name, post_name
                    ));
                }
            }
        }

        // 10. Solve total verification checks programmatically
        for annotated_idx in total_checks {
            let annotated_name = get_sentence_name(annotated_idx, library);
            let solver = Solver::new();

            // Build programmatic total check logic: assert F(Ok(x)) == Panic
            let x = Dynamic::new_const("x", val_sort);
            
            // ok_x = Ok(x)
            let ok_x = ok_con.apply(&[&x]);

            // annotated_app = F_out_0(ok_x)
            let annotated_decl = &sentence_decls[&annotated_idx][0];
            let annotated_app = annotated_decl.apply(&[&ok_x]);

            // Assert is_panic(annotated_app)
            let is_panic_tester = &sorts[1].variants[1].tester;
            let is_panic_bool = is_panic_tester.apply(&[&annotated_app]).as_bool().unwrap();
            solver.assert(&is_panic_bool);

            match solver.check() {
                SatResult::Unsat => {
                    println!(
                        "[PASS] '{}' is total (never panics)",
                        annotated_name
                    );
                }
                SatResult::Sat => {
                    let mut error_msg = format!(
                        "'{}' is not total (can panic)",
                        annotated_name
                    );
                    let mut counterexample = String::new();
                    if let Some(model) = solver.get_model() {
                        if let Some(val) = model.eval(&x, true) {
                            let rendered = format_model_val(
                                &val,
                                &model,
                                &sorts,
                                &tuple_arities,
                                &symbol_names,
                                &float_values,
                            );
                            counterexample = format!(" (Counterexample: x = {})", rendered);
                        }
                    }
                    error_msg.push_str(&counterexample);
                    failed_checks.push(error_msg);
                    println!(
                        "[FAIL] '{}' is not total (can panic)!{}",
                        annotated_name, counterexample
                    );
                }
                SatResult::Unknown => {
                    return Err(format!(
                        "Z3 solver returned Unknown for total check on '{}'",
                        annotated_name
                    ));
                }
            }
        }

        if !failed_checks.is_empty() {
            return Err(format!(
                "Precondition/Postcondition/Total verification failed for {} check(s):\n - {}",
                failed_checks.len(),
                failed_checks.join("\n - ")
            ));
        }

        Ok(())
    })
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

fn get_declared_arity(s_idx: SentenceIndex, library: &Library) -> Option<(usize, usize)> {
    for ann in &library.annotations[s_idx] {
        if let Annotation::Arity(n, m) = ann {
            return Some((*n as usize, *m as usize));
        }
    }
    None
}

fn get_sentence_arity(
    s_idx: SentenceIndex,
    library: &Library,
    arity_map: &mut HashMap<SentenceIndex, (usize, usize)>,
    in_progress: &mut HashSet<SentenceIndex>,
) -> Result<(usize, usize), String> {
    if let Some(&arity) = arity_map.get(&s_idx) {
        return Ok(arity);
    }
    if !in_progress.insert(s_idx) {
        return Err(format!("Recursion detected for sentence: {}", get_sentence_name(s_idx, library)));
    }

    let (declared_in, _declared_out) = get_declared_arity(s_idx, library).unwrap_or_else(|| {
        if let Some(Some(arities)) = library.instruction_arities.get(s_idx) {
            if !arities.is_empty() {
                return (arities[0].inputs() as usize, 0);
            }
        }
        (0, 0)
    });

    let mut stack = Vec::new();
    for i in 0..declared_in {
        stack.push(format!("in_{}", i));
    }
    
    let mut inputs_needed = declared_in;

    for inst in &library.sentences[s_idx] {
        match inst {
            Instruction::Push(_) => {
                stack.push("val".to_string());
            }
            Instruction::Drop(n) => {
                let n = *n;
                while stack.len() < n + 1 {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                stack.remove(stack.len() - 1 - n);
            }
            Instruction::Pick(n) => {
                let n = *n;
                while stack.len() < n + 1 {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                let val = stack[stack.len() - 1 - n].clone();
                stack.push(val);
            }
            Instruction::Roll(n) => {
                let n = *n;
                while stack.len() < n + 1 {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                let val = stack.remove(stack.len() - 1 - n);
                stack.push(val);
            }
            Instruction::Tuple(n) => {
                let n = *n;
                for _ in 0..n {
                    stack.pop();
                }
                stack.push("tuple".to_string());
            }
            Instruction::Untuple(n) => {
                let n = *n;
                stack.pop();
                for _ in 0..n {
                    stack.push("component".to_string());
                }
            }
            Instruction::Jump(target) => {
                let (n_t, m_t) = get_sentence_arity(*target, library, arity_map, in_progress)?;
                while stack.len() < n_t {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                for _ in 0..n_t {
                    stack.pop();
                }
                for _ in 0..m_t {
                    stack.push("result".to_string());
                }
            }
            Instruction::Branch(then_t, else_t) => {
                while stack.len() < 1 {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                stack.pop(); // cond

                let (n_then, m_then) = get_sentence_arity(*then_t, library, arity_map, in_progress)?;
                let (n_else, m_else) = get_sentence_arity(*else_t, library, arity_map, in_progress)?;

                let max_n = std::cmp::max(n_then, n_else);
                while stack.len() < max_n {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                for _ in 0..max_n {
                    stack.pop();
                }
                let max_m = std::cmp::max(m_then, m_else);
                for _ in 0..max_m {
                    stack.push("branch_result".to_string());
                }
            }
            Instruction::Add | Instruction::Subtract | Instruction::Multiply | Instruction::Divide | Instruction::Modulo |
            Instruction::Equal | Instruction::Less | Instruction::Greater | Instruction::And | Instruction::Or => {
                while stack.len() < 2 {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                stack.pop();
                stack.pop();
                stack.push("op_result".to_string());
            }
            Instruction::Negate | Instruction::Not | Instruction::IsInt | Instruction::IsBool |
            Instruction::IsSymbol | Instruction::IsFloat | Instruction::IsTuple |
            Instruction::TupleLength | Instruction::SymbolLen | Instruction::SymbolCharAt => {
                let n_ops = match inst {
                    Instruction::SymbolCharAt => 2,
                    _ => 1,
                };
                while stack.len() < n_ops {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                for _ in 0..n_ops {
                    stack.pop();
                }
                stack.push("op_result".to_string());
            }
            Instruction::Panic => {
                // Aborts execution, doesn't affect stack layout
            }
            Instruction::Assert => {
                while stack.len() < 1 {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                stack.pop();
            }
            Instruction::AssertEqual => {
                while stack.len() < 2 {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                stack.pop();
                stack.pop();
            }
            Instruction::Print => {
                while stack.len() < 1 {
                    stack.insert(0, format!("in_inferred_{}", inputs_needed));
                    inputs_needed += 1;
                }
                stack.pop();
            }
        }
    }
    
    let res = (inputs_needed, stack.len());
    arity_map.insert(s_idx, res);
    in_progress.remove(&s_idx);
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assembly::assemble;

    #[test]
    fn test_precondition_verification() {
        let code = r#"
            function safe_for_foo {
                is_int
            }

            #[precondition(safe_for_foo)]
            function foo {
                push 1
                add
            }
        "#;
        let library = assemble(code).unwrap();
        let res = check_precondition(&library);
        assert!(res.is_ok());
    }

    #[test]
    fn test_precondition_invalid_arity() {
        let code = r#"
            #[arity(2, 1)]
            sentence safe_invalid {
                add
            }

            #[precondition(safe_invalid)]
            function foo {
                drop 0
                push 1
            }
        "#;
        let library = assemble(code).unwrap();
        let res = check_precondition(&library);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Safety function 'safe_invalid' must have arity 1 -> 1"));
    }

    #[test]
    fn test_postcondition_verification() {
        let code = r#"
            function is_int_fn {
                is_int
            }

            #[precondition(is_int_fn)]
            #[postcondition(is_int_fn)]
            function identity {
                // returns the input, which is checked to be an int
            }
        "#;
        let library = assemble(code).unwrap();
        let res = check_precondition(&library);
        assert!(res.is_ok());
    }

    #[test]
    fn test_postcondition_verification_fails() {
        let code = r#"
            function is_int_fn {
                is_int
            }
            
            function is_bool_fn {
                is_bool
            }

            #[precondition(is_int_fn)]
            #[postcondition(is_bool_fn)]
            function identity {
                // returns an int (due to precondition), but postcondition expects a bool
            }
        "#;
        let library = assemble(code).unwrap();
        let res = check_precondition(&library);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("postcondition 'is_bool_fn' can fail"));
    }

    #[test]
    fn test_total_verification() {
        let code = r#"
            #[total]
            function identity {
                // returns input (no panicking operations)
            }
        "#;
        let library = assemble(code).unwrap();
        let res = check_precondition(&library);
        assert!(res.is_ok());
    }

    #[test]
    fn test_total_verification_fails() {
        let code = r#"
            #[total]
            function add_one {
                push 1
                add // panics if input is not int/float
            }
        "#;
        let library = assemble(code).unwrap();
        let res = check_precondition(&library);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("is not total (can panic)"));
    }
}
