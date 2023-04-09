use std::collections::HashMap;

#[derive(Clone, Debug)]
enum BinaryOp {
    Add, And, Eq
}

/// A list of untyped expressions
#[derive(Clone, Debug)]
enum Exp {
    Num(f64), Bool(bool), Unit,
    Ident(String),
    Binary(BinaryOp, Box<Self>, Box<Self>),
    Call {
        func: Box<Self>,
        args: Vec<Self>,
    },
    Lambda {
        args: Vec<(String, Option<Type>)>,
        ret: Option<Type>,
        body: Box<Self>,
    },
    Define {
        name: String,
        ty: Option<Type>,
        value: Box<Self>,
    },
    Let {
        name: String,
        ty: Option<Type>,
        value: Box<Self>,
        body: Box<Self>,
    },
    If {
        cond: Box<Self>,
        t: Box<Self>,
        f: Box<Self>,
    },
}

impl std::fmt::Display for Exp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Exp::*;
        match self {
            Num(n) => write!(f, "{n}"),
            Bool(b) => write!(f, "{b}"),
            Unit => write!(f, "()"),
            Ident(s) => write!(f, "{s}"),
            Binary(op, lhs, rhs) => {
                write!(f, "{lhs} {} {rhs}", match op {
                    BinaryOp::Add => "+",
                    BinaryOp::And => "&&",
                    BinaryOp::Eq => "==",
                }, lhs = lhs, rhs = rhs)
            },
            Call { func, args } => {
                match &**func {
                    Ident(s) => write!(f, "{s}(")?,
                    _ => write!(f, "({func})(")?,
                }
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            },
            Lambda { args, ret, body } => {
                write!(f, "\\")?;
                for (i, (arg, ty)) in args.iter().enumerate() {
                    if i > 0 { write!(f, " ")?; }
                    write!(f, "{arg}")?;
                    if let Some(ty) = ty {
                        write!(f, ": {ty}")?;
                    }
                }
                if let Some(ret) = ret {
                    write!(f, ": {ret}")?;
                }
                write!(f, " -> {body}")
            },
            Define { name, ty, value } => {
                write!(f, "let {name}")?;
                if let Some(ty) = ty {
                    write!(f, ": {ty}")?;
                }
                write!(f, " = {value}")
            },
            Let { name, ty, value, body } => {
                write!(f, "let {name}")?;
                if let Some(ty) = ty {
                    write!(f, ": {ty}")?;
                }
                write!(f, " = {value} in {body}")
            },
            If { cond, t, f: fb } => {
                write!(f, "if {cond} then {t} else {fb}")
            },
        }
    }
}

/// A list of typed expressions
#[derive(Clone, Debug)]
enum TExp {
    Num(f64), Bool(bool), Unit,
    Ident(String),
    Binary(BinaryOp, Box<Self>, Box<Self>, Type),
    Call {
        func: Box<Self>,
        args: Vec<Self>,
    },
    Lambda {
        args: Vec<(String, Type)>,
        ret: Type,
        body: Box<Self>,
    },
    Define {
        name: String,
        ty: Type,
        value: Box<Self>,
    },
    Let {
        name: String,
        ty: Type,
        value: Box<Self>,
        body: Box<Self>,
    },
    If {
        cond: Box<Self>,
        t: Box<Self>,
        f: Box<Self>,
        ret: Type,
    },
}

impl std::fmt::Display for TExp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use TExp::*;
        match self {
            Num(n) => write!(f, "{n}"),
            Bool(b) => write!(f, "{b}"),
            Unit => write!(f, "()"),
            Ident(s) => write!(f, "{s}"),
            Binary(op, lhs, rhs, _ty) => {
                write!(f, "{lhs} {} {rhs}", match op {
                    BinaryOp::Add => "+",
                    BinaryOp::And => "&&",
                    BinaryOp::Eq => "==",
                })
            },
            Call { func, args } => {
                match &**func {
                    Ident(s) => write!(f, "{s}(")?,
                    _ => write!(f, "({func})(")?,
                }
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            },
            Lambda { args, ret, body } => {
                write!(f, "\\")?;
                for (i, (arg, ty)) in args.iter().enumerate() {
                    if i > 0 { write!(f, " ")?; }
                    write!(f, "({arg}: {ty})")?;
                }
                write!(f, ": {ret} -> {body}")
            },
            Define { name, ty, value } => {
                write!(f, "let {name}: {ty} = {value}")
            },
            Let { name, ty, value, body } => {
                write!(f, "let {name}: {ty} = {value} in {body}")
            },
            If { cond, t, f: fb, .. } => {
                write!(f, "if {cond} then {t} else {fb}")
            },
        }
    }
}

/// All possible types
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Type {
    // Literal types
    Num, Bool, Unit,
    // An unbound variable type ('a, 'b etc.)
    Var(usize),
    // A function type (A -> B)
    Fun {
        args: Vec<Self>,
        ret: Box<Self>,
    },
    // Constructor type (T<A>)
    Constructor {
        name: String,
        generics: Vec<Self>,
    },
}

/// Convert a number to a string of lowercase letters
///
///     0 -> a, 1 -> b, ... 24 -> y, 25 -> z,
///     26 -> aa, 27 -> ab, ... 51 -> az, 52 -> ba, ...
///
/// This is to replace the type variable usize index
/// with a string like in OCaml for readability
fn itoa(i: usize) -> String {
    let mut s = String::new();
    let mut i = i;

    while i >= 26 {
        s.push((b'a' + (i % 26) as u8) as char);
        i /= 26;
    }
    s.push((b'a' + i as u8) as char);
    s
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Type::*;
        match self {
            Num => write!(f, "Num"),
            Bool => write!(f, "Bool"),
            Unit => write!(f, "()"),
            Var(i) => write!(f, "'{}", itoa(*i)),
            Fun { args, ret } => {
                write!(f, "(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ") => {ret}")
            },
            Constructor { name, generics } => {
                write!(f, "{name}")?;
                if !generics.is_empty() {
                    write!(f, "<")?;
                    for generic in generics {
                        write!(f, "{generic} ")?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            },
        }
    }
}

#[derive(Clone, Debug)]
struct Infer {
    // List of substitutions ($0 => T, $1 => U, ...)
    subst: Vec<Type>,
    // List of type constraints (T = U, U = V, ...)
    constraints: Vec<(Type, Type)>,
    // Type environment
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

    /// Generate a fresh type variable
    fn fresh(&mut self) -> Type {
        let i = self.subst.len();
        self.subst.push(Type::Var(i));
        Type::Var(i)
    }

    /// Get a substitution for a type variable
    fn subst(&self, i: usize) -> Option<Type> {
        self.subst.get(i).cloned()
    }

    /// Check if a type variable occurs in a type
    ///
    ///     occurs('a, ('a -> 'b)) -> true
    ///     occurs('c, ('a -> 'b)) -> false
    ///     occurs('a, Num)        -> false
    ///
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

    /// Unify two types
    /// Unify is the process of finding a substitution that makes two types equal
    ///
    ///     unify('a, Num) -> 'a = Num
    ///
    fn unify(&mut self, t1: Type, t2: Type) -> Result<(), String> {
        use Type::*;
        match (t1, t2) {
            // Literal types
            (Num, Num) | (Bool, Bool) | (Unit, Unit) => Ok(()),

            // Variable
            (Var(i), Var(j)) if i == j => Ok(()), // Same variables can be unified
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
                // Check the number of arguments
                if a1.len() != a2.len() {
                    return Err(format!("Function argument mismatch: {} != {}", a1.len(), a2.len()));
                }
                // Unify the arguments
                for (a1, a2) in a1.into_iter().zip(a2.into_iter()) {
                    self.unify(a1, a2)?;
                }
                // Unify the return types
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

    /// Solve the constraints by unifying them
    fn solve(&mut self) -> Result<(), String> {
        // Unify the constraints
        for (t1, t2) in self.constraints.clone().into_iter() {
            self.unify(t1, t2)?;
        }
        Ok(())
    }

    /// Substitute the type variables with the substitutions
    ///
    ///     substitute(['a -> Num], 'a) -> Num
    ///     substitute(['a -> 'b], 'a)  -> 'b
    ///
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

    /// Find a type variable in (typed) expression and substitute them
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
            If { cond, t, f, ret } => {
                let ct = self.substitute_texp(*cond);
                let tt = self.substitute_texp(*t);
                let ft = self.substitute_texp(*f);
                If {
                    cond: Box::new(ct),
                    t: Box::new(tt),
                    f: Box::new(ft),
                    ret: self.substitute(ret),
                }
            },
        }
    }

    /// Infer the type of an expression
    fn infer(&mut self,
        e: Exp,
        expected: Type,
    ) -> Result<TExp, String> {
        use Exp::*;
        match e {
            // Literal values
            // Push the constraint (expected type to be the literal type) and
            // return the typed expression
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

            // Identifiers
            // The same as literals but the type is looked up in the environment
            Ident(ref x) => {
                let t = self.env.get(x).ok_or(format!("Unbound variable: {}", x))?;
                self.constraints.push((expected, t.clone()));
                Ok(TExp::Ident(x.clone()))
            }

            // Binary operators
            // The type of the left and right hand side are inferred and
            // the expected type is determined by the operator
            Binary(op, lhs, rhs) => match op {
                // Numeric operators
                BinaryOp::Add => {
                    let lt = self.infer(*lhs, Type::Num)?;
                    let rt = self.infer(*rhs, Type::Num)?;
                    self.constraints.push((expected, Type::Num));
                    Ok(TExp::Binary(op, Box::new(lt), Box::new(rt), Type::Num))
                },
                // Boolean operators
                BinaryOp::And => {
                    let lt = self.infer(*lhs, Type::Bool)?;
                    let rt = self.infer(*rhs, Type::Bool)?;
                    self.constraints.push((expected, Type::Bool));
                    Ok(TExp::Binary(op, Box::new(lt), Box::new(rt), Type::Bool))
                },
                // 'a -> 'a -> 'a operators
                BinaryOp::Eq => {
                    // Create a fresh type variable and then use it as the
                    // expected type for both the left and right hand side
                    // so the type on both side have to be the same
                    let t = self.fresh();
                    let lt = self.infer(*lhs, t.clone())?;
                    let rt = self.infer(*rhs, t)?;
                    self.constraints.push((expected, Type::Bool));
                    Ok(TExp::Binary(op, Box::new(lt), Box::new(rt), Type::Bool))
                },
            }

            // Application or function call
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
            // Lambda
            Lambda { args, ret, body } => {
                // Get the return type or create a fresh type variable
                let rt = ret.unwrap_or(self.fresh());
                // Fill in the type of the arguments with a fresh type
                let xs = args.into_iter()
                    .map(|(x, t)| (x, t.unwrap_or(self.fresh())))
                    .collect::<Vec<(String, Type)>>();

                // Create a new environment, and add the arguments to it
                // and use the new environment to infer the body
                let mut env = self.env.clone();
                xs.clone().into_iter().for_each(|(x, t)| { env.insert(x, t); });
                let mut inf = self.clone();
                inf.env = env;
                let bt = inf.infer(*body, rt.clone())?;

                // Add the substitutions & constraints from the body
                // if it doesn't already exist
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
            // Define (or let expression without a body)
            Define { name, ty, value } => {
                let t = ty.unwrap_or(self.fresh());
                let vt = self.infer(*value, t.clone())?;
                self.env.insert(name.clone(), t.clone());

                // Define always returns unit
                self.constraints.push((expected, Type::Unit));

                Ok(TExp::Define {
                    name,
                    ty: t,
                    value: Box::new(vt),
                })
            },
            // A let expression
            Let { name, ty, value, body } => {
                // Infer the type of the value
                let t = ty.unwrap_or(self.fresh());
                let vt = self.infer(*value, t.clone())?;

                // Create a new environment and add the binding to it
                // and then use the new environment to infer the body
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
            // If expression
            If { cond, t, f } => {
                // Condition has to be a boolean
                let ct = self.infer(*cond, Type::Bool)?;
                // The type of the if expression is the same as the
                // expected type
                let tt = self.infer(*t, expected.clone())?;
                let et = self.infer(*f, expected.clone())?;

                Ok(TExp::If {
                    cond: Box::new(ct),
                    t: Box::new(tt),
                    f: Box::new(et),
                    ret: expected,
                })
            },
        }
    }
}

/// Infer a list of expressions
fn infer_exprs(es: Vec<Exp>) -> (Vec<TExp>, String) {
    let mut inf = Infer::new();
    // Typed expressions
    let mut tes = vec![];
    // Typed expressions without substitutions
    let mut tes_nosub = vec![];
    // Errors
    let mut errs = vec![];

    for e in es {
        let f = inf.fresh();
        let t = inf.infer(e, f).unwrap();
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
    // None means that the expression has an error
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
    tes_union.clone().into_iter()
        .for_each(|te| r.traverse(te));

    (
        tes_union.into_iter()
            .map(|te| r.rename_texp(te))
            .collect::<Vec<TExp>>(),
        errs.join("\n")
    )
}

/// A renamer to rename type variables to a "minimized" form for more readable output
///
///     \(x: '4) (y: '2): '4 => \(x: '0) (y: '1): '0
///     \(f: ('9 -> '15)) (a: '14): '15 => \(f: ('0 -> '1)) (a: '2): '1
///
struct Renamer {
    // Type variables encountered so far
    // We can use it as a mapping by using the index of the
    // vector as key
    // e.g. \(x: '4) (y: '2): '4
    //      [4, 2] so vars[0] is 4 and vars[1] is 2
    vars: Vec<usize>,
}

impl Renamer {
    fn new() -> Self {
        Self {
            vars: vec![],
        }
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

macro_rules! num { ($n:expr) => { Exp::Num($n) } }
macro_rules! bool { ($b:expr) => { Exp::Bool($b) } }
macro_rules! ident { ($i:expr) => { Exp::Ident($i.to_string()) } }
macro_rules! binary {
    ($op:expr, $lhs:expr, $rhs:expr $(,)?) => {
        Exp::Binary($op, Box::new($lhs), Box::new($rhs))
    }
}
macro_rules! call {
    ($f:expr, $($a:expr),*) => {
        Exp::Call {
            func: Box::new($f),
            args: vec![$($a),*],
        }
    }
}
macro_rules! lambda {
    ($($x:expr),* => $body:expr, $ret:expr $(,)?) => {
        Exp::Lambda {
            args: vec![$(($x.to_string(), None)),*],
            ret: $ret,
            body: Box::new($body),
        }
    };
}
macro_rules! define {
    ($name:expr, $ty:expr, $value:expr $(,)?) => {
        Exp::Define {
            name: $name.to_string(),
            ty: $ty,
            value: Box::new($value),
        }
    };
}
macro_rules! let_ {
    ($name:expr, $ty:expr, $value:expr, $body:expr $(,)?) => {
        Exp::Let {
            name: $name.to_string(),
            ty: $ty,
            value: Box::new($value),
            body: Box::new($body),
        }
    };
}
macro_rules! if_ {
    ($cond:expr, $t:expr, $f:expr $(,)?) => {
        Exp::If {
            cond: Box::new($cond),
            t: Box::new($t),
            f: Box::new($f),
        }
    };
}

fn main() {
    /*
    let id = \x -> x;
    let a = 15 + id(10);
    let x = 34 in
        a + x;
     */
    // let es = vec![
    //     define!("id", None, lambda!("x" => ident!("x"), None)),
    //     define!("a", None, binary!(BinaryOp::Add, num!(15.0), call!(ident!("id"), num!(10.0)))),
    //     let_!("x", None, num!(34.0), binary!(BinaryOp::Add, ident!("a"), ident!("x"))),
    // ];

    /*
    let id = \x -> x;
    let compose = \f g x -> f(g(x));
     */
    // let es = vec![
    //     define!("id", None, lambda!("x" => ident!("x"), None)),
    //     define!("compose", None,
    //         lambda!("f", "g", "x" =>
    //             call!(ident!("f"), call!(ident!("g"), ident!("x"))),
    //             None)),
    // ];

    /*
    let f = \w x y z -> w(x(y), z);
    let add = \x y -> x + y;
    let id = \x -> x;
    let a = f(add, id, 10, 20);
     */
    // let es = vec![
    //     define!("f", None,
    //         lambda!("w", "x", "y", "z" =>
    //             call!(ident!("w"), call!(ident!("x"), ident!("y")), ident!("z")),
    //             None)),
    //     define!("add", None,
    //         lambda!("x", "y" =>
    //             binary!(BinaryOp::Add, ident!("x"), ident!("y")),
    //             None)),
    //     define!("id", None, lambda!("x" => ident!("x"), None)),
    //     define!("a", None,
    //         call!(ident!("f"),
    //             ident!("add"), ident!("id"), num!(10.0), num!(20.0))),
    // ];

    // \w x y z -> w(x(y), z);
    // let es = vec![lambda!("w", "x", "y", "z" =>
    //     call!(ident!("w"), call!(ident!("x"), ident!("y")), ident!("z")),
    //     None
    // )];

    // def a = def b = 10;
    let es = vec![
        define!("a", None, define!("b", None, num!(10.0))),
    ];

    let start = std::time::Instant::now();
    let (tes, e) = infer_exprs(es.clone());
    let end = std::time::Instant::now();
    println!(
        "{}\x1b[0mType inference took {}s",
        match e.is_empty() {
            true => "\x1b[92mOK! ",
            false => "\x1b[91mERR! ",
        },
        (end - start).as_secs_f64()
    );

    println!("\x1b[95;1mExpressions:\x1b[0m");
    for e in es {
        println!("{e}");
    }

    if !tes.is_empty() {
        println!("\x1b[94;1mTyped expressions:\x1b[0m");
        for te in tes {
            println!("{te}");
        }
    }
    if !e.is_empty() {
        println!("\x1b[91;1mErrors:\x1b[0m");
        println!("{e}");
    }
}