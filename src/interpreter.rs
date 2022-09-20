//! Lisp interpreter

use crate::parser::{AtomicSymbol, LispExpr, SExpression};

/// Environment for the interpreter
#[derive(Eq, PartialEq, Debug)]
struct Environment {
    // The pairs, in reverse order
    reverse_pairs: Vec<(AtomicSymbol, LispExpr)>,
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
    /// The operation is undefined for with the given arguments.
    UndefinedOperation(LispExpr),
}

impl Environment {
    /// The lookup function returns the first expressions from the list in the environment that
    /// matches the given atomic symbol (name).
    /// Returns an error if the symbol is not defined.
    fn lookup(self: &Self, atom_name: &AtomicSymbol) -> Result<&LispExpr, InterpreterError> {
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
    fn put_in_front(self: &mut Self, atom_name: AtomicSymbol, expr: LispExpr) {
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
fn eval<'a>(expr: &'a LispExpr, env: &'a Environment) -> Result<Environment, InterpreterError> {
    match expr {
        LispExpr::SExpr(sexpr) => match sexpr {
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
        },
        LispExpr::MExpr(_fname, _exprs) => {
            todo!("not implemented")
        }
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
        let val = LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("VAL")));
        env.put_in_front(key.clone(), val);
        let actual = env.lookup(&key);
        assert_eq!(
            Ok(&LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from(
                "VAL"
            )))),
            actual
        );
    }

    #[test]
    fn environment_lookup_must_return_first_defined_symbol() {
        let mut env = Environment::default();
        let key = AtomicSymbol::from("KEY");
        env.put_in_front(
            key.clone(),
            LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("V1"))),
        );
        env.put_in_front(
            key.clone(),
            LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("V2"))),
        );
        let actual = env.lookup(&key);
        assert_eq!(
            Ok(&LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from(
                "V2"
            )))),
            actual
        );
    }

    #[test]
    fn environment_lookup_must_return_error_for_undefined_symbol() {
        let env = Environment::default();
        let key = AtomicSymbol::from("KEY");
        let actual = env.lookup(&key);
        assert_eq!(Err(InterpreterError::UndefinedVariable(key)), actual);
    }

    #[test]
    #[ignore]
    fn eval_mexpr_atom_of_atom_must_be_true() {
        let env = Environment::default();
        let actual = eval(
            &LispExpr::MExpr(
                String::from("atom"),
                vec![LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("X")))],
            ),
            &env,
        );
        // TODO: assert_eq!(true, actual);
    }

    #[test]
    #[ignore]
    fn eval_mexpr_atom_of_pair_must_be_false() {
        let env = Environment::default();
        let actual = eval(
            &LispExpr::MExpr(
                String::from("atom"),
                vec![LispExpr::SExpr(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("X"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                ))],
            ),
            &env,
        );
        // TODO: assert_eq!(false, actual);
    }
}
