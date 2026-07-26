// SMT-LIB2 generator and Z3 executor for safety contracts

use std::collections::{HashMap, HashSet};
use std::process::Command;
use std::io::Write;
use std::fs::File;
use super::formula::{Formula, Expr};

// =============================================================================
// Variable Collection
// =============================================================================

pub fn collect_vars_formula(f: &Formula, vars: &mut HashSet<String>) {
    match f {
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
            collect_vars_formula(a, vars);
            collect_vars_formula(b, vars);
        }
        Formula::Not(a) => collect_vars_formula(a, vars),
        Formula::Equal(a, b) | Formula::NotEqual(a, b) => {
            collect_vars_expr(a, vars);
            collect_vars_expr(b, vars);
        }
        Formula::Expr(e) => collect_vars_expr(e, vars),
    }
}

pub fn collect_vars_expr(e: &Expr, vars: &mut HashSet<String>) {
    match e {
        Expr::Var(name) => {
            vars.insert(name.clone());
        }
        Expr::In(idx) | Expr::InField(idx, _) => {
            vars.insert(format!("in_{}", idx));
        }
        Expr::Out(idx) | Expr::OutField(idx, _) => {
            vars.insert(format!("out_{}", idx));
        }
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Mod(a, b) |
        Expr::LessThan(a, b) | Expr::LessThanEqual(a, b) | Expr::Equal(a, b) => {
            collect_vars_expr(a, vars);
            collect_vars_expr(b, vars);
        }
        Expr::Neg(a) | Expr::Not(a) | Expr::Field(a, _) => {
            collect_vars_expr(a, vars);
        }
        Expr::Call(_, args) => {
            for arg in args {
                collect_vars_expr(arg, vars);
            }
        }
        Expr::Formula(f) => collect_vars_formula(f, vars),
        Expr::Tuple(elms) => {
            for elm in elms {
                collect_vars_expr(elm, vars);
            }
        }
        Expr::Cond(c, t, el) => {
            collect_vars_expr(c, vars);
            collect_vars_expr(t, vars);
            collect_vars_expr(el, vars);
        }
        _ => {}
    }
}

// =============================================================================
// SMT-LIB2 Translator
// =============================================================================

pub fn translate_formula(f: &Formula, float_to_id: &mut HashMap<String, usize>, tuple_to_id: &mut HashMap<Expr, usize>) -> String {
    match f {
        Formula::And(a, b) => format!("(and {} {})", translate_formula(a, float_to_id, tuple_to_id), translate_formula(b, float_to_id, tuple_to_id)),
        Formula::Or(a, b) => format!("(or {} {})", translate_formula(a, float_to_id, tuple_to_id), translate_formula(b, float_to_id, tuple_to_id)),
        Formula::Implies(a, b) => format!("(=> {} {})", translate_formula(a, float_to_id, tuple_to_id), translate_formula(b, float_to_id, tuple_to_id)),
        Formula::Not(a) => format!("(not {})", translate_formula(a, float_to_id, tuple_to_id)),
        Formula::Equal(a, b) => format!("(= {} {})", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Formula::NotEqual(a, b) => format!("(not (= {} {}))", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Formula::Expr(e) => {
            match e {
                Expr::Bool(b) => b.to_string(),
                Expr::Call(name, _) if name == "is_numeric" || name == "is_bool" || name == "is_symbol" || name == "is_int" || name == "is_tuple" => {
                    translate_expr(e, float_to_id, tuple_to_id)
                }
                Expr::LessThan(_, _) | Expr::LessThanEqual(_, _) | Expr::Equal(_, _) => {
                    translate_expr(e, float_to_id, tuple_to_id)
                }
                _ => format!("(getBool {})", translate_expr(e, float_to_id, tuple_to_id)),
            }
        }
    }
}

pub fn translate_expr(e: &Expr, float_to_id: &mut HashMap<String, usize>, tuple_to_id: &mut HashMap<Expr, usize>) -> String {
    match e {
        Expr::Int(val) => format!("(ValInt {})", val),
        Expr::Bool(b) => format!("(ValBool {})", b),
        Expr::Float(f) => {
            let next_id = float_to_id.len();
            let id = *float_to_id.entry(f.clone()).or_insert(next_id);
            format!("(ValFloat {})", id)
        }
        Expr::Var(name) => {
            if name.contains("::") {
                format!("|{}|", name)
            } else {
                name.clone()
            }
        }
        Expr::In(idx) => format!("in_{}", idx),
        Expr::Out(idx) => format!("out_{}", idx),
        Expr::InField(idx, field) => format!("(get_tuple_element in_{} {})", idx, field),
        Expr::OutField(idx, field) => format!("(get_tuple_element out_{} {})", idx, field),
        Expr::Field(inner, field) => format!("(get_tuple_element {} {})", translate_expr(inner, float_to_id, tuple_to_id), field),
        Expr::Add(a, b) => format!("(ValInt (+ (getInt {}) (getInt {})))", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Expr::Sub(a, b) => format!("(ValInt (- (getInt {}) (getInt {})))", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Expr::Mul(a, b) => format!("(ValInt (* (getInt {}) (getInt {})))", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Expr::Div(a, b) => format!("(ValInt (div (getInt {}) (getInt {})))", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Expr::Mod(a, b) => format!("(ValInt (mod (getInt {}) (getInt {})))", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Expr::Neg(a) => format!("(ValInt (- (getInt {})))", translate_expr(a, float_to_id, tuple_to_id)),
        Expr::Not(a) => format!("(ValBool (not (getBool {})))", translate_expr(a, float_to_id, tuple_to_id)),
        Expr::Call(name, args) => {
            if name == "is_numeric" {
                let arg = translate_expr(&args[0], float_to_id, tuple_to_id);
                format!("(or (is-ValInt {}) (is-ValFloat {}))", arg, arg)
            } else if name == "is_bool" {
                format!("(is-ValBool {})", translate_expr(&args[0], float_to_id, tuple_to_id))
            } else if name == "is_symbol" {
                format!("(is-ValSymbol {})", translate_expr(&args[0], float_to_id, tuple_to_id))
            } else if name == "is_int" {
                format!("(is-ValInt {})", translate_expr(&args[0], float_to_id, tuple_to_id))
            } else if name == "is_tuple" {
                let arg = translate_expr(&args[0], float_to_id, tuple_to_id);
                if args.len() == 2 {
                    let len_val = translate_expr(&args[1], float_to_id, tuple_to_id);
                    format!("(and (is-ValTuple {}) (= (get_tuple_len {}) {}))", arg, arg, len_val)
                } else {
                    format!("(is-ValTuple {})", arg)
                }
            } else if name == "len" {
                format!("(get_tuple_len {})", translate_expr(&args[0], float_to_id, tuple_to_id))
            } else if name == "symbol_len" {
                format!("(get_symbol_len {})", translate_expr(&args[0], float_to_id, tuple_to_id))
            } else if name == "char_at" {
                format!("(get_char_at {} {})", translate_expr(&args[0], float_to_id, tuple_to_id), translate_expr(&args[1], float_to_id, tuple_to_id))
            } else if name == "symbol" {
                match &args[0] {
                    Expr::Int(val) => format!("(ValSymbol {})", val),
                    other => format!("(ValSymbol (getInt {}))", translate_expr(other, float_to_id, tuple_to_id)),
                }
            } else {
                let args_smt: Vec<String> = args.iter().map(|a| translate_expr(a, float_to_id, tuple_to_id)).collect();
                format!("({} {})", name, args_smt.join(" "))
            }
        }
        Expr::Formula(f) => format!("(ValBool {})", translate_formula(f, float_to_id, tuple_to_id)),
        Expr::Cond(c, t, el) => {
            format!("(ite (getBool {}) {} {})", translate_expr(c, float_to_id, tuple_to_id), translate_expr(t, float_to_id, tuple_to_id), translate_expr(el, float_to_id, tuple_to_id))
        }
        Expr::LessThan(a, b) => format!("(< (getInt {}) (getInt {}))", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Expr::LessThanEqual(a, b) => format!("(<= (getInt {}) (getInt {}))", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Expr::Equal(a, b) => format!("(= {} {})", translate_expr(a, float_to_id, tuple_to_id), translate_expr(b, float_to_id, tuple_to_id)),
        Expr::Tuple(_) => {
            let next_id = tuple_to_id.len();
            let id = *tuple_to_id.entry(e.clone()).or_insert(next_id);
            format!("(ValTuple {})", id)
        }
    }
}

pub fn collect_tuple_assertions(
    e: &Expr,
    tuple_to_id: &mut HashMap<Expr, usize>,
    float_to_id: &mut HashMap<String, usize>,
    assertions: &mut Vec<String>,
) {
    match e {
        Expr::Tuple(elms) => {
            let next_id = tuple_to_id.len();
            let id = *tuple_to_id.entry(e.clone()).or_insert(next_id);
            assertions.push(format!("(assert (= (get_tuple_len (ValTuple {})) (ValInt {})))", id, elms.len()));
            for (i, elm) in elms.iter().enumerate() {
                let elm_smt = translate_expr(elm, float_to_id, tuple_to_id);
                assertions.push(format!("(assert (= (get_tuple_element (ValTuple {}) {}) {}))", id, i, elm_smt));
                collect_tuple_assertions(elm, tuple_to_id, float_to_id, assertions);
            }
        }
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Mod(a, b) |
        Expr::LessThan(a, b) | Expr::LessThanEqual(a, b) | Expr::Equal(a, b) | Expr::Cond(_, a, b) => {
            collect_tuple_assertions(a, tuple_to_id, float_to_id, assertions);
            collect_tuple_assertions(b, tuple_to_id, float_to_id, assertions);
        }
        Expr::Neg(a) | Expr::Not(a) | Expr::Field(a, _) => {
            collect_tuple_assertions(a, tuple_to_id, float_to_id, assertions);
        }
        Expr::Call(_, args) => {
            for arg in args {
                collect_tuple_assertions(arg, tuple_to_id, float_to_id, assertions);
            }
        }
        Expr::Formula(f) => {
            collect_tuple_assertions_formula(f, tuple_to_id, float_to_id, assertions);
        }
        _ => {}
    }
}

pub fn collect_tuple_assertions_formula(
    f: &Formula,
    tuple_to_id: &mut HashMap<Expr, usize>,
    float_to_id: &mut HashMap<String, usize>,
    assertions: &mut Vec<String>,
) {
    match f {
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
            collect_tuple_assertions_formula(a, tuple_to_id, float_to_id, assertions);
            collect_tuple_assertions_formula(b, tuple_to_id, float_to_id, assertions);
        }
        Formula::Not(a) => {
            collect_tuple_assertions_formula(a, tuple_to_id, float_to_id, assertions);
        }
        Formula::Equal(a, b) | Formula::NotEqual(a, b) => {
            collect_tuple_assertions(a, tuple_to_id, float_to_id, assertions);
            collect_tuple_assertions(b, tuple_to_id, float_to_id, assertions);
        }
        Formula::Expr(e) => {
            collect_tuple_assertions(e, tuple_to_id, float_to_id, assertions);
        }
    }
}

// =============================================================================
// Z3 Process Invocation
// =============================================================================

pub fn check_with_z3(pc: &Formula, query: &Formula) -> Result<bool, String> {
    let prelude = r#"
(declare-datatypes () ((Val 
  (ValInt (getInt Int))
  (ValBool (getBool Bool))
  (ValFloat (getFloat Int))
  (ValSymbol (getSymbol Int))
  (ValTuple (getTupleId Int))
)))

(declare-fun get_tuple_element (Val Int) Val)
(declare-fun get_tuple_len (Val) Val)
(declare-fun get_symbol_len (Val) Val)
(declare-fun get_char_at (Val Val) Val)

(assert (forall ((v Val)) (is-ValInt (get_tuple_len v))))
(assert (forall ((s Val)) (is-ValInt (get_symbol_len s))))
(assert (forall ((s Val) (i Val)) (is-ValInt (get_char_at s i))))
"#;

    let mut vars = HashSet::new();
    collect_vars_formula(pc, &mut vars);
    collect_vars_formula(query, &mut vars);

    let mut float_to_id = HashMap::new();
    let mut tuple_to_id = HashMap::new();

    // Pre-insert empty tuple to ensure it gets an ID and has its assertions generated
    let empty_expr = Expr::Tuple(Vec::new());
    let empty_id = *tuple_to_id.entry(empty_expr.clone()).or_insert(0);

    let pc_smt = translate_formula(pc, &mut float_to_id, &mut tuple_to_id);
    let query_smt = translate_formula(query, &mut float_to_id, &mut tuple_to_id);

    let mut assertions = Vec::new();
    collect_tuple_assertions_formula(pc, &mut tuple_to_id, &mut float_to_id, &mut assertions);
    collect_tuple_assertions_formula(query, &mut tuple_to_id, &mut float_to_id, &mut assertions);

    // Explicitly add assertion for the empty tuple ID length
    assertions.push(format!("(assert (= (get_tuple_len (ValTuple {})) (ValInt 0)))", empty_id));
    // Add the empty tuple uniqueness axiom
    assertions.push(format!(
        "(assert (forall ((x Val)) (=> (and (is-ValTuple x) (= (get_tuple_len x) (ValInt 0))) (= x (ValTuple {})))))",
        empty_id
    ));

    let mut script = String::new();
    script.push_str(prelude);
    script.push_str("\n");
    for var in vars {
        let decl_name = if var.contains("::") {
            format!("|{}|", var)
        } else {
            var.clone()
        };
        script.push_str(&format!("(declare-fun {} () Val)\n", decl_name));
    }
    for assertion in assertions {
        script.push_str(&assertion);
        script.push_str("\n");
    }
    script.push_str(&format!("(assert {})\n", pc_smt));
    script.push_str(&format!("(assert (not {}))\n", query_smt));
    script.push_str("(check-sat)\n");

    let thread_id = format!("{:?}", std::thread::current().id());
    let thread_num: String = thread_id.chars().filter(|c| c.is_ascii_digit()).collect();
    let tmp_path = std::env::temp_dir().join(format!("hanoi_safety_{}.smt2", thread_num));
    {
        let mut file = File::create(&tmp_path).map_err(|e| e.to_string())?;
        file.write_all(script.as_bytes()).map_err(|e| e.to_string())?;
    }

    let output = Command::new("z3")
        .arg(&tmp_path)
        .output();

    match output {
        Ok(out) => {
            let stdout = String::from_utf8_lossy(&out.stdout);
            let result = stdout.trim();
            if result.starts_with("unsat") {
                Ok(true) // Valid
            } else if result.starts_with("sat") {
                Ok(false) // Invalid
            } else {
                Err(format!("Z3 returned unexpected result: {}\nError: {}\nGenerated SMT Script:\n{}", stdout, String::from_utf8_lossy(&out.stderr), script))
            }
        }
        Err(err) => {
            Err(format!("Failed to execute Z3 SMT solver: {}", err))
        }
    }
}
