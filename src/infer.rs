use std::collections::HashMap;
use crate::{renamer::Renamer, exp::{BinaryOp, Exp, TExp, Type, itoa}};

#[derive(Clone, Debug)]
struct Infer {
    // Substitution [$0 => T, $1 => U, ...]
    subst: Vec<Type>,
    // Type constraints [T = U, U = V, ...]
    constraints: Vec<(Type, Type)>,
    // Environment
    env: HashMap<String, Type>,
}

impl Infer {
    fn new() -> Self {
        Self {
            subst: Vec::new(),
            constraints: Vec::new(),
            env: HashMap::new(),
        }
    }

    fn fresh(&mut self) -> Type {
        let i = self.subst.len();
        self.subst.push(Type::Var(i));
        Type::Var(i)
    }

    fn subst(&self, i: usize) -> Option<Type> {
        self.subst.get(i).cloned()
    }

    fn occurs(&self, i: usize, t: Type) -> bool {
        use Type::*;
        match t {
            Num | Bool | Unit => false,
            Var(j) => {
                if let Some(t) = self.subst(j) {
                    if t != Var(j) {
                        return self.occurs(i, t);
                    }
                }
                i == j
            },
            Fun { args, ret } => {
                args.into_iter().any(|t| self.occurs(i, t)) || self.occurs(i, *ret)
            },
            Constructor { generics, .. } => {
                generics.into_iter().any(|t| self.occurs(i, t))
            },
        }
    }

    fn unify(&mut self, t1: Type, t2: Type) -> Result<(), String> {
        use Type::*;
        match (t1, t2) {
            // Literal types
            (Num, Num) | (Bool, Bool) | (Unit, Unit) => Ok(()),

            // Variable
            (Var(i), Var(j)) if i == j => Ok(()),
            (Var(i), t2) => {
                // If the substitution is not the variable itself,
                // unify the substitution with t2
                if let Some(t) = self.subst(i) {
                    if t != Var(i) {
                        return self.unify(t, t2);
                    }
                }
                // If the variable occurs in t2
                if self.occurs(i, t2.clone()) {
                    return Err(format!("Infinite type: '{} = {}", itoa(i), t2));
                }
                // Set the substitution
                self.subst[i] = t2;
                Ok(())
            },
            (t1, Var(i)) => {
                if let Some(t) = self.subst(i) {
                    if t != Var(i) {
                        return self.unify(t1, t);
                    }
                }
                if self.occurs(i, t1.clone()) {
                    return Err(format!("Infinite type: '{} = {}", itoa(i), t1));
                }
                self.subst[i] = t1;
                Ok(())
            },

            // Function
            (Fun { args: a1, ret: r1 }, Fun { args: a2, ret: r2 }) => {
                if a1.len() != a2.len() {
                    return Err(format!("Function argument mismatch: {} != {}", a1.len(), a2.len()));
                }
                for (a1, a2) in a1.into_iter().zip(a2.into_iter()) {
                    self.unify(a1, a2)?;
                }
                self.unify(*r1, *r2)
            },

            // Constructor
            (Constructor { name: n1, generics: g1 }, Constructor { name: n2, generics: g2 }) => {
                // Check if the constructor names are the same
                if n1 != n2 {
                    return Err(format!("Constructor name mismatch: {} != {}", n1, n2));
                }
                // Check the number of generics
                if g1.len() != g2.len() {
                    return Err(format!("Constructor generic mismatch: {} != {}", g1.len(), g2.len()));
                }
                // Unify the generics
                for (g1, g2) in g1.into_iter().zip(g2.into_iter()) {
                    self.unify(g1, g2)?;
                }
                Ok(())
            },

            // The rest will be type mismatch
            (t1, t2) => Err(format!("Type mismatch: {} != {}", t1, t2)),
        }
    }

    fn solve(&mut self) -> Result<(), String> {
        // Unify the constraints
        for (t1, t2) in self.constraints.clone().into_iter() {
            self.unify(t1, t2)?;
        }
        Ok(())
    }

    fn substitute(&mut self, t: Type) -> Type {
        use Type::*;
        match t {
            // Variable
            Var(i) => {
                // If the substitution is not the variable itself,
                // substitute the substitution
                if let Some(t) = self.subst(i) {
                    if t != Var(i) {
                        return self.substitute(t);
                    }
                }
                // Otherwise, return the variable itself
                Var(i)
            },
            // Function
            Fun { args, ret } => {
                Fun {
                    // Substitute the arguments and return type
                    args: args.into_iter().map(|t| self.substitute(t)).collect(),
                    ret: Box::new(self.substitute(*ret)),
                }
            },
            // Constructor
            Constructor { name, generics } => {
                Constructor {
                    name,
                    // Substitute the generics
                    generics: generics.into_iter().map(|t| self.substitute(t)).collect(),
                }
            },
            // The rest will be returned as is
            _ => t,
        }
    }

    fn substitute_texp(&mut self, e: TExp) -> TExp {
        use TExp::*;
        match e {
            Num(_) | Bool(_) | Unit | Ident(_) => e,
            Binary(op, lhs, rhs, t) => {
                let lt = self.substitute_texp(*lhs);
                let rt = self.substitute_texp(*rhs);
                Binary(op, Box::new(lt), Box::new(rt), t)
            },
            Call { func, args } => {
                let ft = self.substitute_texp(*func);
                let xs = args.into_iter()
                    .map(|e| self.substitute_texp(e))
                    .collect::<Vec<TExp>>();
                Call {
                    func: Box::new(ft),
                    args: xs,
                }
            },
            Lambda { args, ret, body } => {
                let rt = self.substitute(ret);
                let xs = args.into_iter()
                    .map(|(x, t)| (x, self.substitute(t)))
                    .collect::<Vec<(String, Type)>>();
                let bt = self.substitute_texp(*body);
                Lambda {
                    args: xs,
                    ret: rt,
                    body: Box::new(bt)
                }
            },
            Define { name, ty, value } => {
                let vt = self.substitute_texp(*value);
                Define {
                    name,
                    ty: self.substitute(ty),
                    value: Box::new(vt),
                }
            },
            Let { name, ty, value, body } => {
                let vt = self.substitute_texp(*value);
                let bt = self.substitute_texp(*body);
                Let {
                    name,
                    ty: self.substitute(ty),
                    value: Box::new(vt),
                    body: Box::new(bt),
                }
            },
        }
    }

    fn infer(&mut self,
        e: Exp,
        expected: Type,
    ) -> Result<TExp, String> {
        use Exp::*;
        match e {
            Num(x) => {
                self.constraints.push((expected, Type::Num));
                Ok(TExp::Num(x))
            },
            Bool(x) => {
                self.constraints.push((expected, Type::Bool));
                Ok(TExp::Bool(x))
            },
            Unit => {
                self.constraints.push((expected, Type::Unit));
                Ok(TExp::Unit)
            },

            Ident(ref x) => {
                let t = self.env.get(x).ok_or(format!("Unbound variable: {}", x))?;
                self.constraints.push((expected, t.clone()));
                Ok(TExp::Ident(x.clone()))
            }

            Binary(op, lhs, rhs) => match op {
                BinaryOp::Add => {
                    let lt = self.infer(*lhs, Type::Num)?;
                    let rt = self.infer(*rhs, Type::Num)?;
                    self.constraints.push((expected, Type::Num));
                    Ok(TExp::Binary(op, Box::new(lt), Box::new(rt), Type::Num))
                },
                BinaryOp::And => {
                    let lt = self.infer(*lhs, Type::Bool)?;
                    let rt = self.infer(*rhs, Type::Bool)?;
                    self.constraints.push((expected, Type::Bool));
                    Ok(TExp::Binary(op, Box::new(lt), Box::new(rt), Type::Bool))
                },
                BinaryOp::Eq => {
                    let t = self.fresh();
                    let lt = self.infer(*lhs, t.clone())?;
                    let rt = self.infer(*rhs, t)?;
                    self.constraints.push((expected, Type::Bool));
                    Ok(TExp::Binary(op, Box::new(lt), Box::new(rt), Type::Bool))
                },
            }

            Call { func, args } => {
                // Generate fresh types for the arguments
                let freshes = args.clone().into_iter()
                    .map(|_| self.fresh())
                    .collect::<Vec<Type>>();
                // Create a function type
                let fsig = Type::Fun {
                    args: freshes.clone(),
                    ret: Box::new(expected),
                };
                // Expect the function to have the function type
                let ft = self.infer(*func, fsig)?;
                // Infer the arguments
                let xs = args.into_iter()
                    .zip(freshes.into_iter())
                    .map(|(e, t)| self.infer(e, t))
                    .collect::<Result<Vec<TExp>, String>>()?;

                Ok(TExp::Call {
                    func: Box::new(ft),
                    args: xs,
                })
            },
            Lambda { args, ret, body } => {
                let rt = ret.unwrap_or(self.fresh());
                // Fill in the type of the arguments
                let xs = args.into_iter()
                    .map(|(x, t)| (x, t.unwrap_or(self.fresh())))
                    .collect::<Vec<(String, Type)>>();

                // Create a new environment, and add the arguments to it
                // and use the new environment to infer the body
                let mut env = self.env.clone();
                xs.clone().into_iter().for_each(|(x, t)| {
                    env.insert(x, t);
                });

                let mut inf = self.clone();
                inf.env = env;
                let bt = inf.infer(*body, rt.clone())?;

                // Add the substitutions & constraints from the body
                for s in inf.subst {
                    if !self.subst.contains(&s) {
                        self.subst.push(s);
                    }
                }
                for c in inf.constraints {
                    if !self.constraints.contains(&c) {
                        self.constraints.push(c);
                    }
                }

                // Push the constraints
                self.constraints.push((expected, Type::Fun {
                    args: xs.clone().into_iter()
                        .map(|x| x.1)
                        .collect(),
                    ret: Box::new(rt.clone()),
                }));

                Ok(TExp::Lambda {
                    args: xs,
                    body: Box::new(bt),
                    ret: rt,
                })
            },
            Define { name, ty, value } => {
                let t = ty.unwrap_or(self.fresh());
                let vt = self.infer(*value, t.clone())?;
                self.env.insert(name.clone(), t.clone());
                Ok(TExp::Define {
                    name,
                    ty: t,
                    value: Box::new(vt),
                })
            },
            Let { name, ty, value, body } => {
                let t = ty.unwrap_or(self.fresh());
                let vt = self.infer(*value, t.clone())?;

                let mut env = self.env.clone();
                env.insert(name.clone(), t.clone());

                let mut inf = Infer::new();
                inf.env = env;
                let bt = inf.infer(*body, expected)?;

                Ok(TExp::Let {
                    name,
                    ty: t,
                    value: Box::new(vt),
                    body: Box::new(bt),
                })
            },
        }
    }
}

pub fn infer_exprs(es: Vec<Exp>) -> (Vec<TExp>, String) {
    let mut inf = Infer::new();
    // Typed expressions
    let mut tes = vec![];
    // Typed expressions without substitutions
    let mut tes_nosub = vec![];
    // Errors
    let mut errs = vec![];
    for e in es {
        let f = inf.fresh();
        let t = inf.infer(e, f).expect("Infer failed");
        tes.push(Some(t.clone()));
        tes_nosub.push(t.clone());

        match inf.solve() {
            Ok(_) => {
                // Substitute the type variables for the solved expressions
                tes = tes.into_iter()
                    .map(|x| x.map(|t| inf.substitute_texp(t)))
                    .collect();
            },
            Err(e) => {
                errs.push(e);
                // Replace the expression with None
                tes.pop();
                tes.push(None);
            },
        }
    }

    // Union typed expressions, replacing None with the typed expression without substitutions
    let mut tes_union = vec![];
    for (te, te_nosub) in tes.into_iter().zip(tes_nosub.into_iter()) {
        match te {
            Some(t) => {
                tes_union.push(t);
            },
            None => {
                tes_union.push(te_nosub);
            },
        }
    }

    let mut r = Renamer::new();
    let t = r.process(tes_union);

    (
        t,
        errs.join("\n")
    )
}