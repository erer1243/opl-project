// e ::= v | (e e..) | (if e e e)
#[derive(Clone)]
pub enum JExpr {
    JVal(JValue),
    JIf {
        ec: Box<JExpr>,
        et: Box<JExpr>,
        ef: Box<JExpr>,
    },
    JApply {
        p: Box<JExpr>,
        args: Vec<JExpr>,
    },
}

// v ::= number | boolean | prim
// prim ::= + | * | / | - | <= | < | = | > | >=
// prim is not a separate data structure in my implementation
#[derive(Copy, Clone)]
pub enum JValue {
    Num(i32),
    Bool(bool),
    Plus,
    Minus,
    Mult,
    Div,
    LtEq,
    Lt,
    Eq,
    Gt,
    GtEq,
}

impl JExpr {
    // Convenience function to make constructing JExpr::JIf cleaner
    pub fn jif(ec: JExpr, et: JExpr, ef: JExpr) -> JExpr {
        let ec = Box::new(ec);
        let et = Box::new(et);
        let ef = Box::new(ef);

        JExpr::JIf { ec, et, ef }
    }

    // Convenience function to make constructing JExpr::JApply cleaner
    pub fn japply(p: JExpr, args: &[JExpr]) -> JExpr {
        let p = Box::new(p);
        let args = args.into();

        JExpr::JApply { p, args }
    }
}

// K ::= KRet | (KIf e e K) | (KApp (v..) (e..) K)
// Aka Continuation
pub enum Cont {
    KRet,
    KIf {
        et: JExpr,
        ef: JExpr,
        k: Box<Cont>,
    },
    KApp {
        v: Vec<JValue>,
        e: Vec<JExpr>,
        k: Box<Cont>,
    },
}

impl Cont {
    // Convenience function to make constructing Cont::KIf cleaner
    pub fn kif(et: JExpr, ef: JExpr, k: Cont) -> Cont {
        Cont::KIf {
            et,
            ef,
            k: k.into(),
        }
    }

    // Convenience function to make constructing Cont::KApp cleaner
    pub fn kapp(v: &[JValue], e: &[JExpr], k: Cont) -> Cont {
        Cont::KApp {
            v: v.into(),
            e: e.into(),
            k: k.into(),
        }
    }
}
