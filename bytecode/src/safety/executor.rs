// Symbolic Execution Engine for Hanoi safety contracts

use std::collections::HashMap;
use crate::library::{Library, SentenceIndex, Annotation};
use crate::value::Value;
use crate::opcode::Instruction;
use super::formula::{Formula, Expr, substitute_formula};

#[derive(Clone)]
pub struct SymbolicState {
    pub stack: Vec<Expr>,
    pub pc: Formula,
    pub vcs: Vec<Formula>,
    pub inlining_stack: Vec<SentenceIndex>,
    pub var_counter: usize,
}

pub fn execute_instruction_symbolic(
    inst: &Instruction,
    library: &Library,
    state: &mut SymbolicState,
) -> Result<(), String> {
    match inst {
        Instruction::Push(val) => {
            let expr = value_to_expr(val, &library.symbols)?;
            state.stack.push(expr);
        }
        Instruction::Drop(n) => {
            if state.stack.len() <= *n {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            state.stack.remove(state.stack.len() - 1 - *n);
        }
        Instruction::Pick(n) => {
            if state.stack.len() <= *n {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let idx = state.stack.len() - 1 - *n;
            let val = state.stack[idx].clone();
            state.stack.push(val);
        }
        Instruction::Roll(n) => {
            if state.stack.len() <= *n {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let idx = state.stack.len() - 1 - *n;
            let val = state.stack.remove(idx);
            state.stack.push(val);
        }
        Instruction::Equal => {
            if state.stack.len() < 2 {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let b = state.stack.pop().unwrap();
            let a = state.stack.pop().unwrap();
            state.stack.push(Expr::Formula(Box::new(Formula::Equal(Box::new(a), Box::new(b)))));
        }
        Instruction::Greater | Instruction::Less => {
            if state.stack.len() < 2 {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let b = state.stack.pop().unwrap();
            let a = state.stack.pop().unwrap();

            // Safety VC: both numeric
            let is_num_a = Formula::Expr(Expr::Call("is_numeric".to_string(), vec![a.clone()]));
            let is_num_b = Formula::Expr(Expr::Call("is_numeric".to_string(), vec![b.clone()]));
            let safety = Formula::And(Box::new(is_num_a), Box::new(is_num_b));
            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(safety)));

            let res = match inst {
                Instruction::Greater => Expr::LessThan(Box::new(b), Box::new(a)), // a > b <=> b < a
                Instruction::Less => Expr::LessThan(Box::new(a), Box::new(b)),
                _ => unreachable!(),
            };
            state.stack.push(res);
        }
        Instruction::Add | Instruction::Subtract | Instruction::Multiply | Instruction::Divide | Instruction::Modulo => {
            if state.stack.len() < 2 {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let b = state.stack.pop().unwrap();
            let a = state.stack.pop().unwrap();

            // Safety VC: both numeric
            let is_num_a = Formula::Expr(Expr::Call("is_numeric".to_string(), vec![a.clone()]));
            let is_num_b = Formula::Expr(Expr::Call("is_numeric".to_string(), vec![b.clone()]));
            let mut safety = Formula::And(Box::new(is_num_a), Box::new(is_num_b));

            if matches!(inst, Instruction::Divide | Instruction::Modulo) {
                // b != 0
                let non_zero = Formula::NotEqual(Box::new(b.clone()), Box::new(Expr::Int(0)));
                safety = Formula::And(Box::new(safety), Box::new(non_zero));
            }

            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(safety)));

            let res = match inst {
                Instruction::Add => Expr::Add(Box::new(a), Box::new(b)),
                Instruction::Subtract => Expr::Sub(Box::new(a), Box::new(b)),
                Instruction::Multiply => Expr::Mul(Box::new(a), Box::new(b)),
                Instruction::Divide => Expr::Div(Box::new(a), Box::new(b)),
                Instruction::Modulo => Expr::Mod(Box::new(a), Box::new(b)),
                _ => unreachable!(),
            };
            state.stack.push(res);
        }
        Instruction::Not => {
            if state.stack.is_empty() {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let a = state.stack.pop().unwrap();

            // Safety VC: is boolean
            let is_bool = Formula::Expr(Expr::Call("is_bool".to_string(), vec![a.clone()]));
            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(is_bool)));

            state.stack.push(Expr::Not(Box::new(a)));
        }
        Instruction::Negate => {
            if state.stack.is_empty() {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let a = state.stack.pop().unwrap();

            // Safety VC: is numeric
            let is_num = Formula::Expr(Expr::Call("is_numeric".to_string(), vec![a.clone()]));
            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(is_num)));

            state.stack.push(Expr::Neg(Box::new(a)));
        }
        Instruction::Print => {
            if state.stack.is_empty() {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            state.stack.pop();
        }
        Instruction::Panic => {
            // Unconditional panic path must be proven unreachable!
            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(Formula::Expr(Expr::Bool(false)))));
        }
        Instruction::Assert => {
            if state.stack.is_empty() {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let cond = state.stack.pop().unwrap();

            // Safety VC: cond is true
            let is_bool = Formula::Expr(Expr::Call("is_bool".to_string(), vec![cond.clone()]));
            let is_true = Formula::Expr(cond.clone());
            let safety = Formula::And(Box::new(is_bool), Box::new(is_true));

            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(safety)));
        }
        Instruction::AssertEqual => {
            if state.stack.len() < 2 {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let b = state.stack.pop().unwrap();
            let a = state.stack.pop().unwrap();

            // Safety VC: a == b
            let eq = Formula::Equal(Box::new(a), Box::new(b));
            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(eq)));
        }
        Instruction::Tuple(n) => {
            if state.stack.len() < *n {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let mut elms = Vec::new();
            for _ in 0..*n {
                elms.push(state.stack.pop().unwrap());
            }
            elms.reverse();
            state.stack.push(Expr::Tuple(elms));
        }
        Instruction::Untuple(n) => {
            if state.stack.is_empty() {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let tuple_expr = state.stack.pop().unwrap();

            // Safety VC: must be a tuple with length n
            let is_tup = Formula::Expr(Expr::Call("is_tuple".to_string(), vec![tuple_expr.clone()]));
            let len_check = Formula::Equal(
                Box::new(Expr::Call("len".to_string(), vec![tuple_expr.clone()])),
                Box::new(Expr::Int(*n as i64))
            );
            let safety = Formula::And(Box::new(is_tup), Box::new(len_check));
            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(safety)));

            for i in 0..*n {
                state.stack.push(Expr::Field(Box::new(tuple_expr.clone()), i));
            }
        }
        Instruction::SymbolLen => {
            if state.stack.is_empty() {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let sym = state.stack.pop().unwrap();

            let is_sym = Formula::Expr(Expr::Call("is_symbol".to_string(), vec![sym.clone()]));
            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(is_sym)));

            state.stack.push(Expr::Call("symbol_len".to_string(), vec![sym]));
        }
        Instruction::SymbolCharAt => {
            if state.stack.len() < 2 {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let idx = state.stack.pop().unwrap();
            let sym = state.stack.pop().unwrap();

            let is_sym = Formula::Expr(Expr::Call("is_symbol".to_string(), vec![sym.clone()]));
            let is_i = Formula::Expr(Expr::Call("is_int".to_string(), vec![idx.clone()]));
            let mut safety = Formula::And(Box::new(is_sym), Box::new(is_i));

            let bounds_check_lower = Expr::LessThanEqual(Box::new(Expr::Int(0)), Box::new(idx.clone()));
            let bounds_check_upper = Expr::LessThan(Box::new(idx.clone()), Box::new(Expr::Call("symbol_len".to_string(), vec![sym.clone()])));
            safety = Formula::And(Box::new(safety), Box::new(Formula::And(Box::new(Formula::Expr(bounds_check_lower)), Box::new(Formula::Expr(bounds_check_upper)))));

            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(safety)));
            state.stack.push(Expr::Call("char_at".to_string(), vec![sym, idx]));
        }
        Instruction::Jump(target_idx) => {
            handle_jump(*target_idx, library, state)?;
        }
        Instruction::Branch(then_idx, else_idx) => {
            handle_branch(*then_idx, *else_idx, library, state)?;
        }
        Instruction::And | Instruction::Or => {
            if state.stack.len() < 2 {
                return Err(format!("Stack underflow on instruction {:?}", inst));
            }
            let b = state.stack.pop().unwrap();
            let a = state.stack.pop().unwrap();

            let is_b_a = Formula::Expr(Expr::Call("is_bool".to_string(), vec![a.clone()]));
            let is_b_b = Formula::Expr(Expr::Call("is_bool".to_string(), vec![b.clone()]));
            let safety = Formula::And(Box::new(is_b_a), Box::new(is_b_b));
            state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(safety)));

            let res = match inst {
                Instruction::And => Expr::Formula(Box::new(Formula::And(Box::new(Formula::Expr(a)), Box::new(Formula::Expr(b))))),
                Instruction::Or => Expr::Formula(Box::new(Formula::Or(Box::new(Formula::Expr(a)), Box::new(Formula::Expr(b))))),
                _ => unreachable!(),
            };
            state.stack.push(res);
        }
        Instruction::SetContains | Instruction::SetUnion | Instruction::SetIntersection |
        Instruction::SetDifference | Instruction::SetComplement | Instruction::SetSingleton |
        Instruction::SetTuple(_) | Instruction::SetChoose | Instruction::SetRenamePrefix => {
            return Err(format!("Unsupported deprecated set instruction {:?} encountered during safety checking", inst));
        }
    }
    Ok(())
}

fn handle_jump(target_idx: SentenceIndex, library: &Library, state: &mut SymbolicState) -> Result<(), String> {
    let annotations = &library.annotations[target_idx];
    let mut has_safety = false;
    let mut has_behavior = false;
    let mut safety_contract = Formula::Expr(Expr::Bool(true));
    let mut behavior_contract = Formula::Expr(Expr::Bool(true));

    for ann in annotations {
        match ann {
            Annotation::Safety(s) => {
                has_safety = true;
                safety_contract = super::formula::parse_formula_string(s)?;
            }
            Annotation::Behavior(b) => {
                has_behavior = true;
                behavior_contract = super::formula::parse_formula_string(b)?;
            }
            _ => {}
        }
    }

    if has_safety || has_behavior {
        // Retrieve declared arity
        let mut arity_n = 0;
        let mut arity_m = 0;
        for ann in annotations {
            if let Annotation::Arity(n, m) = ann {
                arity_n = *n as usize;
                arity_m = *m as usize;
            }
        }

        if state.stack.len() < arity_n {
            return Err(format!("Stack underflow on jump to annotated sentence {:?}", target_idx));
        }

        // Map inputs
        let mut inputs = Vec::new();
        for _ in 0..arity_n {
            inputs.push(state.stack.pop().unwrap());
        }
        inputs.reverse(); // top of stack is inputs[0]

        // Assert safety precondition of the target holds
        let subst_safety = substitute_formula(&safety_contract, &inputs, &[]);
        state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(subst_safety)));

        // Generate fresh output variables to represent return values
        let mut outputs = Vec::new();
        let raw_target_idx: usize = target_idx.into();
        for _ in 0..arity_m {
            let out_var = format!("t_{}_{}", raw_target_idx, state.var_counter);
            state.var_counter += 1;
            outputs.push(Expr::Var(out_var));
        }

        // Assume behavior contract of target in path condition
        let subst_behavior = substitute_formula(&behavior_contract, &inputs, &outputs);
        state.pc = Formula::And(Box::new(state.pc.clone()), Box::new(subst_behavior));

        // Push outputs to stack
        for out in outputs {
            state.stack.push(out);
        }
    } else {
        // Unannotated function: inline execution
        if state.inlining_stack.contains(&target_idx) {
            return Err(format!("Recursion/cycle detected during symbolic inlining of unannotated sentence index {:?}", target_idx));
        }
        state.inlining_stack.push(target_idx);
        let instructions = &library.sentences[target_idx];
        for inst in instructions {
            execute_instruction_symbolic(inst, library, state)?;
        }
        state.inlining_stack.pop();
    }
    Ok(())
}

fn handle_branch(then_idx: SentenceIndex, else_idx: SentenceIndex, library: &Library, state: &mut SymbolicState) -> Result<(), String> {
    if state.stack.is_empty() {
        return Err("Stack underflow on branch".to_string());
    }
    let cond = state.stack.pop().unwrap();

    // Safety VC: condition must be boolean
    let is_bool = Formula::Expr(Expr::Call("is_bool".to_string(), vec![cond.clone()]));
    state.vcs.push(Formula::Implies(Box::new(state.pc.clone()), Box::new(is_bool)));

    // Symbolic Execution of Then path
    let mut state_then = state.clone();
    state_then.pc = Formula::And(
        Box::new(state_then.pc),
        Box::new(Formula::Equal(Box::new(cond.clone()), Box::new(Expr::Bool(true))))
    );
    handle_jump(then_idx, library, &mut state_then)?;

    // Symbolic Execution of Else path
    let mut state_else = state.clone();
    state_else.pc = Formula::And(
        Box::new(state_else.pc),
        Box::new(Formula::Equal(Box::new(cond.clone()), Box::new(Expr::Bool(false))))
    );
    handle_jump(else_idx, library, &mut state_else)?;

    // Both paths must return same stack size
    if state_then.stack.len() != state_else.stack.len() {
        return Err(format!(
            "Branch paths returned mismatched stack heights: then_branch={} else_branch={}",
            state_then.stack.len(), state_else.stack.len()
        ));
    }

    // Merge stack states using Cond expression
    let common_len = state_then.stack.len();
    let mut merged_stack = Vec::new();
    for i in 0..common_len {
        let t_val = state_then.stack[i].clone();
        let e_val = state_else.stack[i].clone();
        if t_val == e_val {
            merged_stack.push(t_val);
        } else {
            merged_stack.push(Expr::Cond(Box::new(cond.clone()), Box::new(t_val), Box::new(e_val)));
        }
    }
    state.stack = merged_stack;

    // Merge path conditions
    let pc_then_impl = Formula::Implies(
        Box::new(Formula::Equal(Box::new(cond.clone()), Box::new(Expr::Bool(true)))),
        Box::new(state_then.pc.clone())
    );
    let pc_else_impl = Formula::Implies(
        Box::new(Formula::Equal(Box::new(cond.clone()), Box::new(Expr::Bool(false)))),
        Box::new(state_else.pc.clone())
    );
    state.pc = Formula::And(Box::new(pc_then_impl), Box::new(pc_else_impl));

    state.vcs.extend(state_then.vcs);
    state.vcs.extend(state_else.vcs);
    state.var_counter = std::cmp::max(state_then.var_counter, state_else.var_counter);

    Ok(())
}

fn value_to_expr(val: &Value, symbols: &HashMap<String, Value>) -> Result<Expr, String> {
    match val {
        Value::Bool(b) => Ok(Expr::Bool(*b)),
        Value::Int(i) => Ok(Expr::Int(*i)),
        Value::Float(f) => Ok(Expr::Float(f.to_string())),
        Value::Symbol(sym) => Ok(Expr::Call("symbol".to_string(), vec![Expr::Int(sym.id as i64)])),
        Value::Tuple(elements) => {
            let mut elms = Vec::new();
            for e in elements {
                elms.push(value_to_expr(e, symbols)?);
            }
            Ok(Expr::Tuple(elms))
        }
        Value::Set(_) => Err("Deprecated set value type encountered".to_string()),
    }
}
