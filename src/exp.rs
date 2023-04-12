#[derive(Clone, Debug)]
pub enum BinaryOp {
    Add, And, Eq
}

/// A list of untyped expressions
#[derive(Clone, Debug)]
pub enum Exp {
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
pub enum TExp {
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
pub enum Type {
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
pub fn itoa(i: usize) -> String {
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

macro_rules! num { ($n:expr) => { Exp::Num($n) } }
macro_rules! bool { ($b:expr) => { Exp::Bool($b) } }
macro_rules! ident { ($i:expr) => { Exp::Ident($i.to_string()) } }

macro_rules! binary {
    ($op:expr, $lhs:expr, $rhs:expr) => {
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
    ($($x:expr),* => $body:expr, $ret:expr) => {
        Exp::Lambda {
            args: vec![$(($x.to_string(), None)),*],
            ret: $ret,
            body: Box::new($body),
        }
    };
}

macro_rules! define {
    ($name:expr, $ty:expr, $value:expr) => {
        Exp::Define {
            name: $name.to_string(),
            ty: $ty,
            value: Box::new($value),
        }
    };
}

macro_rules! let_ {
    ($name:expr, $ty:expr, $value:expr, $body:expr) => {
        Exp::Let {
            name: $name.to_string(),
            ty: $ty,
            value: Box::new($value),
            body: Box::new($body),
        }
    };
}