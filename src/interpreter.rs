//! Lisp interpreter

use crate::parser::{AtomicSymbol, LispExpr, SExpression};

/// Environment for the interpreter
#[derive(Eq, PartialEq, Debug)]
struct Environment {
    // The pairs, in reverse order
    reverse_pairs: Vec<(AtomicSymbol, SExpression)>,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            reverse_pairs: vec![],
        }
    }
}

/// Error result for evaluating a Lisp expression.
#[derive(Eq, PartialEq, Debug)]
enum InterpreterError {
    // TODO: introduce a value type for the name
    /// We tried to [lookup] an undefined atomic symbol.
    UndefinedVariable(AtomicSymbol),
    /// The operation is undefined with the given arguments.
    UndefinedOperation(String),
}

impl Environment {
    /// The lookup function returns the first expressions from the list in the environment that
    /// matches the given atomic symbol (name).
    /// Returns an error if the symbol is not defined.
    fn lookup(self: &Self, atom_name: &AtomicSymbol) -> Result<&SExpression, InterpreterError> {
        let expr = self
            .reverse_pairs
            .iter()
            .rfind(|(element_name, _expr)| atom_name == element_name);
        match expr {
            Some((_, e)) => Ok(e),
            None => Err(InterpreterError::UndefinedVariable(atom_name.clone())),
        }
    }

    /// Add an atomic symbol to expression binding to the front of
    /// the list in the environment. Mutates the environment.
    fn put_in_front(self: &mut Self, atom_name: AtomicSymbol, expr: SExpression) {
        self.reverse_pairs.push((atom_name, expr));
    }

    // TODO: use the Lisp data structures to implement lookup and put_in_front
}

/// Evaluate a Lisp expression
///
/// From McCarthy:
///
/// 2. `eval[e; a]` has two arguments, an expression `e` to be evaluated, and a list
/// of pairs `a`. The first item of each pair is an atomic symbol, and the second is
/// the expression for which the symbol stands.
///
/// 3. If the expression to be evaluated is atomic, `eval` evaluates whatever is
/// paired with it first on the list `a`.
fn eval<'a>(expr: &'a SExpression, env: &'a Environment) -> Result<SExpression, InterpreterError> {
    match expr {
        SExpression::ATOM(id) => {
            let e = env.lookup(id);
            match e {
                Ok(bound_expr) => eval(bound_expr, env),
                Err(err) => Err(err),
            }
        }
        SExpression::PAIR(_a, _b) => {
            todo!()
        }
    }
}

fn apply<'a>(fname: &String, args: &Vec<LispExpr>) -> Result<SExpression, InterpreterError> {
    let _env = Environment::default();
    let t: SExpression = SExpression::ATOM(AtomicSymbol::from("T"));
    let f: SExpression = SExpression::ATOM(AtomicSymbol::from("F"));
    match fname.as_str() {
        "atom" => match (args.get(0), args.get(1)) {
            (Some(LispExpr::SExpr(SExpression::ATOM(_))), None) => Ok(t),
            (Some(_), None) => Ok(f),
            _ => Err(InterpreterError::UndefinedOperation(fname.clone())),
        },
        _ => todo!("not implemented"),
    }
}

/// Run the interpreter on a Lisp expression, starting with the empty environment.
/// This is the main entry point for the interpreter.
fn interpret(_expr: &LispExpr) -> Result<Environment, InterpreterError> {
    let _env = Environment::default();
    //eval(expr, env)
    todo!("not implemented")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::SExpression;

    #[test]
    fn environment_lookup_must_return_ok_for_defined_symbol() {
        let mut env = Environment::default();
        let key = AtomicSymbol::from("KEY");
        let val = SExpression::ATOM(AtomicSymbol::from("VAL"));
        env.put_in_front(key.clone(), val);
        let actual = env.lookup(&key);
        assert_eq!(Ok(&SExpression::ATOM(AtomicSymbol::from("VAL"))), actual);
    }

    #[test]
    fn environment_lookup_must_return_first_defined_symbol() {
        let mut env = Environment::default();
        let key = AtomicSymbol::from("KEY");
        env.put_in_front(key.clone(), SExpression::ATOM(AtomicSymbol::from("V1")));
        env.put_in_front(key.clone(), SExpression::ATOM(AtomicSymbol::from("V2")));
        let actual = env.lookup(&key);
        assert_eq!(Ok(&SExpression::ATOM(AtomicSymbol::from("V2"))), actual);
    }

    #[test]
    fn environment_lookup_must_return_error_for_undefined_symbol() {
        let env = Environment::default();
        let key = AtomicSymbol::from("KEY");
        let actual = env.lookup(&key);
        assert_eq!(Err(InterpreterError::UndefinedVariable(key)), actual);
    }

    // TODO: test apply

    #[test]
    #[ignore]
    fn eval_mexpr_atom_of_atom_must_be_true() {
        let env = Environment::default();
        let actual = eval(
            /*            &LispExpr::MExpr(
                           String::from("atom"),
                           vec![LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("X")))],
            */
            // atom[X] translated to S-function
            &SExpression::PAIR(
                Box::new(SExpression::ATOM(AtomicSymbol::from("ATOM"))),
                Box::new(SExpression::ATOM(AtomicSymbol::from("X"))),
            ),
            &env,
        );
        assert_eq!(Ok(SExpression::ATOM(AtomicSymbol::from("T"))), actual);
    }

    #[test]
    #[ignore]
    fn eval_mexpr_atom_of_pair_must_be_false() {
        let env = Environment::default();
        let actual = eval(
            // atom[(A B)] translated to S-function
            &SExpression::PAIR(
                Box::new(SExpression::ATOM(AtomicSymbol::from("ATOM"))),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
                )),
            ),
            &env,
        );
        // TODO: assert_eq!(false, actual);
    }
}
