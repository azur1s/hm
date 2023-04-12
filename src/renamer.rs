use crate::exp::{TExp, Type};

/// A renamer to rename type variables to a "minimized" form for more readable output
///
///     \(x: '4) (y: '2): '4 => \(x: '0) (y: '1): '0
///     \(f: ('9 -> '15)) (a: '14): '15 => \(f: ('0 -> '1)) (a: '2): '1
///
pub struct Renamer {
    // Type variables encountered so far
    // We can use it as a mapping by using the index of the
    // vector as key
    // e.g. \(x: '4) (y: '2): '4
    //      [4, 2] so vars[0] is 4 and vars[1] is 2
    vars: Vec<usize>,
}

impl Renamer {
    pub fn new() -> Self {
        Self {
            vars: vec![],
        }
    }

    pub fn process(&mut self, es: Vec<TExp>) -> Vec<TExp> {
        es.clone().into_iter().for_each(|e| self.traverse(e));
        es.into_iter().map(|e| self.rename_texp(e)).collect()
    }

    fn rename_var(&self, i: usize) -> Type {
        let n = self.vars.iter().position(|x| x == &i).unwrap();
        Type::Var(n)
    }

    fn add_var(&mut self, i: usize) {
        if !self.vars.contains(&i) {
            self.vars.push(i);
        }
    }

    fn find_var(&mut self, t: Type) {
        match t {
            Type::Var(i) => {
                self.add_var(i);
            },
            Type::Fun { args, ret } => {
                args.into_iter().for_each(|t| self.find_var(t));
                self.find_var(*ret);
            },
            Type::Constructor { generics, .. } => {
                generics.into_iter().for_each(|t| self.find_var(t));
            },
            _ => {},
        }
    }

    fn traverse(&mut self, e: TExp) {
        match e {
            TExp::Binary(_, lhs, rhs, _ty) => {
                self.traverse(*lhs);
                self.traverse(*rhs);
            },
            TExp::Call { func, args } => {
                self.traverse(*func);
                for arg in args {
                    self.traverse(arg);
                }
            },
            TExp::Lambda { args, body, ret } => {
                for (_, t) in args { self.find_var(t); }
                self.find_var(ret);
                self.traverse(*body);
            },
            TExp::Define { ty, value, .. } => {
                self.find_var(ty);
                self.traverse(*value);
            },
            TExp::Let { ty, value, body, .. } => {
                self.find_var(ty);
                self.traverse(*value);
                self.traverse(*body);
            },
            _ => {},
        }
    }

    fn rename_type(&self, t: Type) -> Type {
        match t {
            Type::Var(i) => self.rename_var(i),
            Type::Fun { args, ret } => {
                Type::Fun {
                    args: args.into_iter().map(|x| self.rename_type(x)).collect(),
                    ret: Box::new(self.rename_type(*ret)),
                }
            },
            Type::Constructor { name, generics } => {
                Type::Constructor {
                    name,
                    generics: generics.into_iter().map(|x| self.rename_type(x)).collect(),
                }
            },
            _ => t,
        }
    }

    fn rename_texp(&self, e: TExp) -> TExp {
        match e {
            TExp::Binary(op, lhs, rhs, ty) => {
                TExp::Binary(op, lhs, rhs, self.rename_type(ty))
            },
            TExp::Call { func, args } => {
                TExp::Call {
                    func: Box::new(self.rename_texp(*func)),
                    args: args.into_iter().map(|x| self.rename_texp(x)).collect(),
                }
            },
            TExp::Lambda { args, body, ret } => {
                TExp::Lambda {
                    args: args.into_iter()
                        .map(|(x, t)| (x, self.rename_type(t)))
                        .collect(),
                    body: Box::new(self.rename_texp(*body)),
                    ret: self.rename_type(ret),
                }
            },
            TExp::Define { name, ty, value } => {
                TExp::Define {
                    name,
                    ty: self.rename_type(ty),
                    value: Box::new(self.rename_texp(*value)),
                }
            },
            TExp::Let { name, ty, value, body } => {
                TExp::Let {
                    name,
                    ty: self.rename_type(ty),
                    value: Box::new(self.rename_texp(*value)),
                    body: Box::new(self.rename_texp(*body)),
                }
            },
            _ => e,
        }
    }
}