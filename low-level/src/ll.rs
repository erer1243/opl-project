mod util;

use derive_more::Deref;
use std::collections::HashMap;
pub use util::*;

// prog ::= d... e
#[derive(Clone, Copy, Debug)]
pub struct JProg(pub List<JDefine>, pub JExpr);

// d ::= define (f x...) e
#[derive(Clone, Copy, Debug)]
pub struct JDefine(pub JFnRef, pub List<JVarRef>, pub JExpr);

// JExpr pointer wrapper type
#[derive(Copy, Clone, Deref, Debug)]
#[deref(forward)]
pub struct JExpr(Leak<JExprBody>);

// e ::= v | (e e..) | (if e e e) | x
#[derive(Copy, Clone, Debug)]
pub enum JExprBody {
    JVal(JValue),
    JIf(JExpr, JExpr, JExpr),
    JApply(JExpr, List<JExpr>),
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
    JExpr(Leak::new(JExprBody::JIf(ec, et, ef)))
}

// Convenience function to make constructing JExpr::JApply cleaner
pub fn japply(e0: JExpr, em: List<JExpr>) -> JExpr {
    JExpr(Leak::new(JExprBody::JApply(e0, em)))
}

// Convenience function to make constructing JExpr::JVal cleaner
pub fn jval(v: JValue) -> JExpr {
    JExpr(Leak::new(JExprBody::JVal(v)))
}

// Convenience function to make constructing JExpr::JVarRef cleaner
pub fn jvarref(vr: JVarRef) -> JExpr {
    JExpr(Leak::new(JExprBody::JVarRef(vr)))
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
    KIf(JExpr, JExpr, Cont),
    KApp(List<JValue>, List<JExpr>, Cont),
}

// Convenience function to make constructing KRet cleaner
pub fn kret() -> Cont {
    Cont(Leak::new(ContBody::KRet))
}

// Convenience function to make constructing KIf cleaner
pub fn kif(et: JExpr, ef: JExpr, k: Cont) -> Cont {
    Cont(Leak::new(ContBody::KIf(et, ef, k)))
}

// Convenience function to make constructing KApp cleaner
pub fn kapp(v: List<JValue>, e: List<JExpr>, k: Cont) -> Cont {
    Cont(Leak::new(ContBody::KApp(v, e, k)))
}

// Ck machine
// st = <e, k>
#[derive(Clone, Debug)]
pub struct Ck(pub Delta, pub JExpr, pub Cont);

type Delta = HashMap<JFnRef, JDefine>;

impl Ck {
    pub fn evaluate(e: JProg) -> JValue {
        let JProg(defns, body) = e;
        let delta = defns
            .to_vec()
            .into_iter()
            .map(|defn| (defn.0, defn))
            .collect();

        let mut ck = Ck(delta, body, kret());
        while !ck.is_finished() {
            ck = ck.step()
        }

        match *ck.1 {
            JExprBody::JVal(v) => v,
            _ => unreachable!()
        }
    }

    // These are the theoretical interface but i'm just using evaluate()
    // pub fn inject(e: JExpr) -> Ck {
    //     Ck(e, kret())
    // }

    // pub fn extract(ck: Ck) -> JValue {
    //     match *ck.0 {
    //         JExprBody::JVal(v) => v,
    //         _ => panic!("extract called on non-jvalue ck: {:?}", ck),
    //     }
    // }

    pub fn is_finished(&self) -> bool {
        matches!((*self.1, *self.2), (JExprBody::JVal(_), ContBody::KRet))
    }

    // Aka the arrow function |-> from lecture 4
    pub fn step(self) -> Ck {
        use ContBody::*;
        use JExprBody::*;
        use JValue::*;

        let Ck(delta, body, orig_k) = self;

        match (*body, *orig_k) {
            // Rule 1
            (JIf(ec, et, ef), _) => Ck(delta, ec, kif(et, ef, orig_k)),

            // Rule 2
            (JVal(JBool(false)), KIf(_et, ef, k)) => Ck(delta, ef, k),

            // Rule 3
            (JVal(_), KIf(et, _ef, k)) => Ck(delta, et, k),

            // Rule 4
            (JApply(e0, em), _) => Ck(delta, e0, kapp([].into(), em, orig_k)),

            // Rule 5
            (JVal(v1), KApp(v, e, k)) if !e.is_empty() => {
                // Reverse-order trick from lecture 4
                let v = cons(v1, v);
                let (e0, em) = e.head_tail().unwrap();
                Ck(delta, *e0, kapp(v, em, k))
            }

            // Rule 6/7
            (JVal(vn), KApp(v, _e, k)) => {
                let v = cons(vn, v);

                // Lazy way to get last element
                if let JFnRef(f) = v.to_vec().last().unwrap() {
                    // Rule 7
                    let JDefine(_f, xs, ebody) = delta[f];
                    let ebody_prime = subst_arrow(xs, v, ebody);
                    Ck(delta, ebody_prime, k)
                } else {
                    // Rule 6
                    Ck(delta, jval(run_delta(v)), k)
                }
            }

            // bottom
            _ => unreachable!(),
        }
    }
}

// Delta expects a list in reverse order, because of the ck machine
// rule 5 reverse-order trick
fn run_delta(list: List<JValue>) -> JValue {
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

// Substitute a single variable into a JExpr
fn subst(var: (JVarRef, JValue), e: JExpr) -> JExpr {
    use JExprBody::*;

    let (x, xv) = var;
    match &*e {
        JIf(ec, et, ef) => jif(subst(var, *ec), subst(var, *et), subst(var, *ef)),
        JApply(e0, em) => {
            let params = em.to_vec().iter().map(|e| subst(var, *e)).collect();
            japply(subst(var, *e0), params)
        }
        JVarRef(y) if x == *y => jval(xv),
        _ => e,
    }
}

// Called by rule 7, so expects vs in reverse order because of rule 5 reverse order trick
fn subst_arrow(xs: List<JVarRef>, vs: List<JValue>, mut e: JExpr) -> JExpr {
    // Lazy impl using vecs for cleaner code
    let xs = xs.to_vec();
    let mut vs = vs.to_vec();
    vs.pop();
    vs.reverse();

    assert_eq!(vs.len(), xs.len(), "bad param count");

    for (x, v) in xs.iter().zip(vs.iter()) {
        e = subst((x, *v), e);
    }

    e
}
