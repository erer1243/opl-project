mod util;

use derive_more::Deref;
pub use util::*;

// prog ::= d... e
pub struct JProg {
    fs: List<JDefine>,
    e: JExpr,
}

// Convenience function to make constructing JProg cleaner
pub fn jprog<FS: IntoList<JDefine>>(fs: FS, e: JExpr) -> JProg {
    JProg { fs: fs.into(), e }
}

// d ::= define (f x...) e
pub struct JDefine {
    f: JFnRef,
    xs: List<JVarRef>,
    e: JExpr,
}

// Convenience function to make constructing JDefine cleaner
pub fn jdefine<XS: IntoList<JVarRef>>(f: JFnRef, xs: XS, e: JExpr) -> JDefine {
    JDefine {
        f,
        xs: xs.into(),
        e,
    }
}

// JExpr pointer wrapper type
#[derive(Copy, Clone, Deref, Debug)]
#[deref(forward)]
pub struct JExpr(Leak<JExprBody>);

// e ::= v | (e e..) | (if e e e) | x
#[derive(Copy, Clone, Debug)]
pub enum JExprBody {
    JVal(JValue),
    JIf { ec: JExpr, et: JExpr, ef: JExpr },
    JApply { e0: JExpr, em: List<JExpr> },
    JVarRef(JVarRef),
}

// v ::= number | boolean | prim | f
// prim ::= + | * | / | - | <= | < | = | > | >=
// prim is not a separate data structure in my implementation
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
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
    JFnRef(JFnRef),
}

// Convenience function to make constructing JExpr::JIf cleaner
pub fn jif(ec: JExpr, et: JExpr, ef: JExpr) -> JExpr {
    JExpr(Leak::new(JExprBody::JIf { ec, et, ef }))
}

// Convenience function to make constructing JExpr::JApply cleaner
pub fn japply<EM: IntoList<JExpr>>(e0: JExpr, em: EM) -> JExpr {
    JExpr(Leak::new(JExprBody::JApply { e0, em: em.into() }))
}

// Convenience function to make constructing JExpr::JVal cleaner
pub fn jval(v: JValue) -> JExpr {
    JExpr(Leak::new(JExprBody::JVal(v)))
}

// x ::= some set of variable names
type JVarRef = &'static str;

// f ::= some set of function names
type JFnRef = &'static str;

#[derive(Copy, Clone, Deref, Debug)]
#[deref(forward)]
pub struct Cont(Leak<ContBody>);

// K ::= KRet | (KIf e e K) | (KApp (v..) (e..) K)
// Aka Continuation
#[derive(Clone, Copy, Debug)]
pub enum ContBody {
    KRet,
    KIf {
        et: JExpr,
        ef: JExpr,
        k: Cont,
    },
    KApp {
        v: List<JValue>,
        e: List<JExpr>,
        k: Cont,
    },
}

// Convenience function to make constructing KRet cleaner
pub fn kret() -> Cont {
    Cont(Leak::new(ContBody::KRet))
}

// Convenience function to make constructing KIf cleaner
pub fn kif(et: JExpr, ef: JExpr, k: Cont) -> Cont {
    Cont(Leak::new(ContBody::KIf { et, ef, k }))
}

// Convenience function to make constructing KApp cleaner
pub fn kapp(v: List<JValue>, e: List<JExpr>, k: Cont) -> Cont {
    Cont(Leak::new(ContBody::KApp { v, e, k }))
}

// Ck machine
// st = <e, k>
#[derive(Clone, Debug)]
pub struct Ck(pub JExpr, pub Cont);

impl Ck {
    pub fn evaluate(e: JExpr) -> JValue {
        let mut ck = Ck::inject(e);
        while !ck.is_finished() {
            ck = ck.step()
        }
        Ck::extract(ck)
    }

    pub fn inject(e: JExpr) -> Ck {
        Ck(e, kret())
    }

    pub fn extract(ck: Ck) -> JValue {
        match *ck.0 {
            JExprBody::JVal(v) => v,
            _ => panic!("extract called on non-jvalue ck: {:?}", ck),
        }
    }

    pub fn is_finished(&self) -> bool {
        matches!((*self.0, *self.1), (JExprBody::JVal(_), ContBody::KRet))
    }

    // Aka the arrow function |-> from lecture 4
    pub fn step(self) -> Ck {
        use ContBody::*;
        use JExprBody::*;
        use JValue::*;

        let orig_k = self.1;

        match (*self.0, *self.1) {
            // Rule 1
            (JIf { ec, et, ef }, _) => Ck(ec, kif(et, ef, orig_k)),

            // Rule 2
            (JVal(JBool(false)), KIf { ef, k, .. }) => Ck(ef, k),

            // Rule 3
            (JVal(_), KIf { et, k, .. }) => Ck(et, k),

            // Rule 4
            (JApply { e0, em }, _) => Ck(e0, kapp([].into(), em, orig_k)),

            // Rule 5
            (JVal(v1), KApp { v, e, k }) if !e.is_empty() => {
                // Reverse-order trick from lecture 4
                let v = cons(v1, v);
                let (e0, em) = e.head_tail().unwrap();
                Ck(e0.clone(), kapp(v, em, k))
            }

            // Rule 6
            (JVal(vn), KApp { v, k, .. }) => {
                let v = cons(vn, v);
                Ck(jval(delta(v)), k)
            }

            // bottom
            _ => unreachable!(),
        }
    }
}

// Delta expects a list in reverse order, because of the ck machine
// rule 5 reverse-order trick
fn delta(list: List<JValue>) -> JValue {
    use JValue::*;

    // Lazy implementation using vec to reverse the list and get clean match code
    let mut vec = list.to_vec();
    vec.reverse();

    match vec[..] {
        [JPlus, JNum(a), JNum(b)] => JNum(a + b),
        [JMinus, JNum(a), JNum(b)] => JNum(a - b),
        [JMult, JNum(a), JNum(b)] => JNum(a * b),
        [JDiv, JNum(a), JNum(b)] => JNum(a / b),
        [JLtEq, JNum(a), JNum(b)] => JBool(a <= b),
        [JLt, JNum(a), JNum(b)] => JBool(a < b),
        [JEq, JNum(a), JNum(b)] => JBool(a == b),
        [JGt, JNum(a), JNum(b)] => JBool(a > b),
        [JGtEq, JNum(a), JNum(b)] => JBool(a >= b),
        _ => panic!("delta hit bottom case, {:?}", vec),
    }
}
