mod util;

use derive_more::{Deref, IsVariant, Unwrap};
use std::cell::Cell;
pub use util::*;

// JExpr pointer wrapper type
#[derive(Copy, Clone, Deref, Debug, PartialEq, Eq)]
#[deref(forward)]
pub struct JExpr(Leak<JExprBody>);

// Types from page 9-2
#[derive(Copy, Clone, Debug, PartialEq, Eq, Unwrap, IsVariant)]
pub enum JExprBody {
    JVal(JValue),
    JIf(JExpr, JExpr, JExpr),
    JApply(JExpr, List<JExpr>),
    JVarRef(JVarRef),
    JCase(JExpr, (JVarRef, JExpr), (JVarRef, JExpr)),
    JAbort(JExpr),
    JThrow(JExpr),
    JTry(JExpr, JExpr),
}

type JVarRef = &'static str;

#[derive(Copy, Clone, Debug, PartialEq, Eq, IsVariant, Unwrap)]
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

    JLambda(JVarRef, List<JVarRef>, JExpr),

    JUnit,
    JPair(Leak<JValue>, Leak<JValue>),
    JInl(Leak<JValue>),
    JInr(Leak<JValue>),
    JPairOp,
    JInlOp,
    JInrOp,
    JFst,
    JSnd,
    JString(JVarRef),
    JStrEq,

    JSigma(Leak<JValue>),
    JBox,
    JUnbox,
    JSetBox,

    // Closure type used in the CEK machine
    // This should never be used anywhere outside of Cek::step
    JClosure(JVarRef, List<JVarRef>, JExpr, Env),
}

macro_rules! jewrap {
    ($body:ident($($arg:expr),*)) => { JExpr(Leak::new(JExprBody::$body($($arg),*))) };
}

// JExpr constructor functions
pub fn jif(ec: JExpr, et: JExpr, ef: JExpr) -> JExpr {
    jewrap!(JIf(ec, et, ef))
}

pub fn japply(e0: JExpr, em: List<JExpr>) -> JExpr {
    jewrap!(JApply(e0, em))
}

pub fn jval(v: JValue) -> JExpr {
    jewrap!(JVal(v))
}

pub fn jvarref(vr: JVarRef) -> JExpr {
    jewrap!(JVarRef(vr))
}

pub fn jcase(e: JExpr, inl: (JVarRef, JExpr), inr: (JVarRef, JExpr)) -> JExpr {
    jewrap!(JCase(e, inl, inr))
}

pub fn jabort(e: JExpr) -> JExpr {
    jewrap!(JAbort(e))
}

pub fn jthrow(e: JExpr) -> JExpr {
    jewrap!(JThrow(e))
}

pub fn jtry(et: JExpr, ec: JExpr) -> JExpr {
    jewrap!(JTry(et, ec))
}

// Continuation pointer wrapper type
#[derive(Copy, Clone, Deref, Debug)]
#[deref(forward)]
pub struct Cont(Leak<ContBody>);

// K ::= KRet | (KIf e e K) | (KApp (v..) (e..) K)
// Aka Continuation
#[derive(Clone, Copy, Debug, IsVariant)]
pub enum ContBody {
    KRet,
    KIf(Env, JExpr, JExpr, Cont),
    KApp(List<JValue>, Env, List<JExpr>, Cont),
    KCase(Env, (JVarRef, JExpr), (JVarRef, JExpr), Cont),
}

// Cont constructor functions
pub fn kret() -> Cont {
    Cont(Leak::new(ContBody::KRet))
}

pub fn kif(env: Env, et: JExpr, ef: JExpr, k: Cont) -> Cont {
    Cont(Leak::new(ContBody::KIf(env, et, ef, k)))
}

pub fn kapp(v: List<JValue>, env: Env, e: List<JExpr>, k: Cont) -> Cont {
    Cont(Leak::new(ContBody::KApp(v, env, e, k)))
}

pub fn kcase(env: Env, inl: (JVarRef, JExpr), inr: (JVarRef, JExpr), k: Cont) -> Cont {
    Cont(Leak::new(ContBody::KCase(env, inl, inr, k)))
}

// Cek machine
// st = <e, k>
#[derive(Clone)]
pub struct Cek(JExpr, Env, Cont);

impl Cek {
    pub fn evaluate(e: JExpr) -> JValue {
        let mut ck = Cek(e, Env::EMPTY, kret());

        while !ck.is_finished() {
            ck = ck.step();
        }

        ck.0.unwrap_j_val()
    }

    fn print_debug(&self) {
        println!("== {:?}", self.0);
        println!("== {:?}", self.1);
        println!("== {:?}", self.2);
        println!();
    }

    fn is_finished(&self) -> bool {
        self.0.is_j_val() && self.2.is_k_ret()
    }

    // Aka the arrow function |-> from lecture 4
    pub fn step(self) -> Cek {
        use ContBody::*;
        use JExprBody::*;
        use JValue::*;

        let Cek(body, env, orig_k) = self;

        // Rules from 6-6 plus lambda/closure rules from 6-11
        match (*body, *orig_k) {
            // Rules 1..5 from 6-6
            (JVarRef(x), _k) => Cek(jval(env.get(x)), Env::EMPTY, orig_k),
            (JIf(ec, et, ef), _k) => Cek(ec, env, kif(env, et, ef, orig_k)),
            (JVal(JBool(false)), KIf(envp, _et, ef, k)) => Cek(ef, envp, k),
            (JVal(_), KIf(envp, et, _ef, k)) => Cek(et, envp, k),
            (JApply(e0, em), _) => Cek(e0, env, kapp([].into(), env, em, orig_k)),

            // Lambda to closure (rule 1) from 6-11
            // Updated to support closures with recurse name, 8-2,8-3
            (JVal(JLambda(f, xs, ebody)), _k) => {
                let mut envp = env.cons((f, JValue::JNum(0)));
                let clos = JClosure(f, xs, ebody, envp);
                envp.update((f, clos));
                Cek(jval(clos), env, orig_k)
            }

            // Rule 6 from 6-6
            // Apply where some parameters need to be evaluated
            (JVal(v1), KApp(v, envp, e, k)) if !e.is_empty() => {
                // Reverse-order trick from lecture 4
                // Values in v are stored in reverse order compared with e
                let v = cons(v1, v);
                let (e0, em) = e.head_tail().unwrap();
                Cek(*e0, envp, kapp(v, envp, em, k))
            }

            // Combination of two rules (6-6 rule 7 and 6-11 rule 2)
            // Apply where all parameters have been evaluated to values
            (JVal(vn), KApp(v, _envp, _e, k)) => {
                let v = cons(vn, v);

                if let JClosure(_f, xs, ebody, envp) = v.last() {
                    // Closure eval (rule 2) from 6-11
                    // apply where we are applying to a closure
                    let env = Env::from_func_apply(envp, xs, v);
                    Cek(ebody, env, k)
                } else {
                    // Rule 7 from 6-6
                    // Apply where we are applying to a prim
                    Cek(run_delta(v), Env::EMPTY, k)
                }
            }

            // Case into kcase continuation, invented from 9-3
            (JCase(e, inl, inr), _k) => Cek(e, env, kcase(env, inl, inr, orig_k)),

            // Case branch rules, invented from 9-3
            (JVal(JInl(v)), KCase(envp, (xl, el), _inr, k)) => Cek(el, envp.cons((xl, *v)), k),
            (JVal(JInr(v)), KCase(envp, _inl, (xr, er), k)) => Cek(er, envp.cons((xr, *v)), k),

            _ => {
                self.print_debug();
                panic!("CEK hit bottom case");
            }
        }
    }
}

// Delta expects a list in reverse order, because of the cek machine
// rule 5 reverse-order trick
fn run_delta(list: List<JValue>) -> JExpr {
    use JValue::*;

    // Lazy implementation using vec to reverse the list and get clean match code
    let mut vec = list.to_vec();
    vec.reverse();

    let v = match vec[..] {
        [JPlus, JNum(a), JNum(b)] => JNum(a + b),
        [JMinus, JNum(a), JNum(b)] => JNum(a - b),
        [JMult, JNum(a), JNum(b)] => JNum(a * b),
        [JDiv, JNum(a), JNum(b)] => JNum(a / b),
        [JLtEq, JNum(a), JNum(b)] => JBool(a <= b),
        [JLt, JNum(a), JNum(b)] => JBool(a < b),
        [JEq, JNum(a), JNum(b)] => JBool(a == b),
        [JGt, JNum(a), JNum(b)] => JBool(a > b),
        [JGtEq, JNum(a), JNum(b)] => JBool(a >= b),

        [JInlOp, v] => JInl(Leak::new(v)),
        [JInrOp, v] => JInr(Leak::new(v)),

        [JPairOp, vl, vr] => JPair(Leak::new(vl), Leak::new(vr)),
        [JFst, JPair(vl, _)] => *vl,
        [JSnd, JPair(_, vr)] => *vr,

        [JStrEq, JString(a), JString(b)] => JBool(a == b),

        [JBox, v] => JSigma(Leak::new(v)),
        [JUnbox, JSigma(l)] => *l,
        [JSetBox, JSigma(l), v] => {
            l.set(v);
            v
        }

        _ => panic!("delta hit bottom case, {:?}", vec),
    };

    jval(v)
}

#[derive(Copy, Clone, Deref, Debug, Eq, PartialEq)]
pub struct Env(List<(JVarRef, Cell<JValue>)>);

impl Env {
    pub const EMPTY: Env = Env(List::new());

    pub fn cons(self, (name, val): (JVarRef, JValue)) -> Env {
        Env(cons((name, Cell::new(val)), *self))
    }

    pub fn update(&mut self, (name, val): (JVarRef, JValue)) {
        let mut curr = **self;

        while let Some(((x, v), next)) = curr.head_tail() {
            if *x == name {
                v.set(val);
                break;
            }
            curr = next;
        }
    }

    pub fn get(self, var_ref: JVarRef) -> JValue {
        let mut curr = *self;

        while let Some(((x, v), next)) = curr.head_tail() {
            if *x == var_ref {
                return v.get();
            }
            curr = next;
        }

        panic!("No var {} in environment", var_ref);
    }

    // Generate an env for a closure body
    // Expects v to be in reverse and contain the closure at the end, so no manipulation of v
    // is needed in Cek::step
    pub fn from_func_apply(mut env: Env, x: List<JVarRef>, v: List<JValue>) -> Env {
        // Lazy impl using vecs for cleaner code
        let x = x.to_vec();
        let mut v = v.to_vec();
        v.pop();
        v.reverse();

        assert_eq!(
            x.len(),
            v.len(),
            "apply expected args {:?} but got {:?}",
            x,
            v
        );

        for (x, v) in x.iter().zip(v.iter()) {
            env = env.cons((*x, *v));
        }
        env
    }
}
