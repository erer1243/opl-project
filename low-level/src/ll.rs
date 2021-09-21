use std::collections::VecDeque;

// e ::= v | (e e..) | (if e e e)
#[derive(Clone, Debug)]
pub enum JExpr {
    JVal(JValue),
    JIf {
        ec: Box<JExpr>,
        et: Box<JExpr>,
        ef: Box<JExpr>,
    },
    JApply {
        e0: Box<JExpr>,
        em: Vec<JExpr>,
    },
}

// v ::= number | boolean | prim
// prim ::= + | * | / | - | <= | < | = | > | >=
// prim is not a separate data structure in my implementation
#[derive(Copy, Clone, Debug)]
pub enum JValue {
    JNum(i32),
    JBool(bool),
    JPlus,
    JMinus,
    JMult,
    JDiv,
    JLtEq,
    JLt,
    JEq,
    JGt,
    JGtEq,
}

impl JExpr {
    // Convenience function to make constructing JExpr::JIf cleaner
    pub fn jif<EC, ET, EF>(ec: EC, et: ET, ef: EF) -> JExpr
    where
        EC: Into<Box<JExpr>>,
        ET: Into<Box<JExpr>>,
        EF: Into<Box<JExpr>>,
    {
        JExpr::JIf {
            ec: ec.into(),
            et: et.into(),
            ef: ef.into(),
        }
    }

    // Convenience function to make constructing JExpr::JApply cleaner
    pub fn japply<E0, EM>(e0: E0, em: EM) -> JExpr
    where
        E0: Into<Box<JExpr>>,
        EM: Into<Vec<JExpr>>,
    {
        JExpr::JApply {
            e0: e0.into(),
            em: em.into(),
        }
    }
}

// K ::= KRet | (KIf e e K) | (KApp (v..) (e..) K)
// Aka Continuation
#[derive(Clone, Debug)]
pub enum Cont {
    KRet,
    KIf {
        et: JExpr,
        ef: JExpr,
        k: Box<Cont>,
    },
    KApp {
        v: Vec<JValue>,
        e: VecDeque<JExpr>, // VecDeque because pop_front is used in Ck::step()
        k: Box<Cont>,
    },
}

impl Cont {
    // Convenience function to make constructing Cont::KIf cleaner
    pub fn kif<K>(et: JExpr, ef: JExpr, k: K) -> Cont
    where
        K: Into<Box<Cont>>,
    {
        Cont::KIf {
            et,
            ef,
            k: k.into(),
        }
    }

    // Convenience function to make constructing Cont::KApp cleaner
    pub fn kapp<V, E, K>(v: V, e: E, k: K) -> Cont
    where
        V: Into<Vec<JValue>>,
        E: Into<VecDeque<JExpr>>,
        K: Into<Box<Cont>>,
    {
        Cont::KApp {
            v: v.into(),
            e: e.into(),
            k: k.into(),
        }
    }
}
