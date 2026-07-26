// Core module for Hanoi Static Safety and Behavior Contract Checker

pub mod formula;
pub mod executor;
pub mod z3;

use crate::library::{Library, SentenceIndex, Annotation};
use formula::{Formula, Expr, parse_formula_string, substitute_formula};
use executor::{SymbolicState, execute_instruction_symbolic};
use z3::check_with_z3;

pub fn check_safety(library: &Library) -> Result<(), String> {
    for (s_idx_raw, annotations) in library.annotations.iter().enumerate() {
        let s_idx = SentenceIndex::from(s_idx_raw);

        let mut has_safety = false;
        let mut has_behavior = false;
        for ann in annotations {
            match ann {
                Annotation::Safety(_) => has_safety = true,
                Annotation::Behavior(_) => has_behavior = true,
                _ => {}
            }
        }

        if has_safety || has_behavior {
            check_sentence_safety(s_idx, library)?;
        }
    }
    Ok(())
}

fn check_sentence_safety(s_idx: SentenceIndex, library: &Library) -> Result<(), String> {
    let annotations = &library.annotations[s_idx];
    let name = &library.names[s_idx];

    let mut arity_n = 0;
    let mut arity_m = 0;
    let mut safety_contract = Formula::Expr(Expr::Bool(true));
    let mut behavior_contract = Formula::Expr(Expr::Bool(true));

    for ann in annotations {
        match ann {
            Annotation::Arity(n, m) => {
                arity_n = *n as usize;
                arity_m = *m as usize;
            }
            Annotation::Safety(s) => {
                safety_contract = parse_formula_string(s)?;
            }
            Annotation::Behavior(b) => {
                behavior_contract = parse_formula_string(b)?;
            }
        }
    }

    // Set up initial symbolic stack
    let mut stack = Vec::new();
    let mut initial_inputs = Vec::new();
    for i in (0..arity_n).rev() {
        let var_name = format!("in_{}", i);
        let var_expr = Expr::Var(var_name);
        stack.push(var_expr.clone());
    }
    for i in 0..arity_n {
        initial_inputs.push(Expr::Var(format!("in_{}", i)));
    }

    let mut state = SymbolicState {
        stack,
        pc: safety_contract.clone(),
        vcs: Vec::new(),
        inlining_stack: vec![s_idx],
        var_counter: 0,
    };

    // Execute the instructions
    let instructions = &library.sentences[s_idx];
    for inst in instructions {
        execute_instruction_symbolic(inst, library, &mut state)?;
    }

    // Assert final arity matches
    if state.stack.len() != arity_m {
        return Err(format!(
            "Safety checker error: after executing '{}', stack size is {} but expected arity {}",
            name, state.stack.len(), arity_m
        ));
    }

    // Assert final postcondition holds
    let mut outputs = Vec::new();
    for _ in 0..arity_m {
        outputs.push(state.stack.pop().unwrap());
    }

    let subst_behavior = substitute_formula(&behavior_contract, &initial_inputs, &outputs);
    state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(subst_behavior)));

    // Verify all collected VCs with Z3
    for vc in &state.vcs {
        match check_with_z3(&Formula::Expr(Expr::Bool(true)), vc) {
            Ok(true) => {} // Valid
            Ok(false) => {
                return Err(format!(
                    "Static safety verification FAILED for sentence '{}'. Could not prove safety condition:\n  {}",
                    name, vc.to_string_pretty()
                ));
            }
            Err(e) => {
                return Err(format!(
                    "Safety checker failed to verify sentence '{}' due to solver error:\n  {}",
                    name, e
                ));
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::assembly::assemble;

    #[test]
    fn test_valid_contracts() {
        let code = r#"
            #[arity(2, 1)]
            #[safety("is_numeric(in[0]) && is_numeric(in[1]) && in[0] != 0")]
            #[behavior("out[0] == in[1] / in[0]")]
            sentence safe_divide {
                divide
            }
        "#;
        let res = assemble(code);
        assert!(res.is_ok(), "Expected valid code to verify: {:?}", res);
    }

    #[test]
    fn test_unsafe_divide() {
        let code = r#"
            #[arity(2, 1)]
            #[safety("is_numeric(in[0]) && is_numeric(in[1])")]
            sentence unsafe_divide {
                divide
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Could not prove safety condition"));
    }

    #[test]
    fn test_assertion_mismatch() {
        let code = r#"
            #[arity(2, 0)]
            #[safety("is_numeric(in[0]) && is_numeric(in[1])")]
            sentence unsafe_assert {
                assert_eq
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Could not prove safety condition"));
    }

    #[test]
    fn test_recursion_cycle_error() {
        let code = r#"
            sentence rec_a {
                jump rec_b
            }
            sentence rec_b {
                jump rec_a
            }
            #[arity(0, 0)]
            #[safety("true")]
            sentence caller {
                jump rec_a
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Recursion/cycle detected"));
    }

    #[test]
    fn test_deprecated_set_choose_error() {
        let code = r#"
            #[arity(1, 1)]
            #[safety("true")]
            sentence use_set_choose {
                set_choose
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Unsupported deprecated set instruction"));
    }
}
