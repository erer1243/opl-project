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
    JCallCC(JExpr),
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

    // aka "v = .. | Kont k" from 13-4
    JCont(Cont),

    JNumberQ,
    JBoxQ,
    JBooleanQ,
    JPairQ,
    JUnitQ,
    JInlQ,
    JInrQ,
    JContinuationQ,
    JFunctionQ,
    JPrimitiveQ,
    JFunctionArity,
    JPrimitiveArity,
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

pub fn jcallcc(e: JExpr) -> JExpr {
    jewrap!(JCallCC(e))
}

pub fn str_to_abort(s: &'static str) -> JExpr {
    jabort(jval(JValue::JString(s)))
}

// Continuation pointer wrapper type
#[derive(Copy, Clone, Deref, Debug, PartialEq, Eq)]
#[deref(forward)]
pub struct Cont(Leak<ContBody>);

// K ::= KRet | (KIf e e K) | (KApp (v..) (e..) K)
// Aka Continuation
#[derive(Clone, Copy, Debug, IsVariant, PartialEq, Eq)]
pub enum ContBody {
    KRet,
    KIf(Env, JExpr, JExpr, Cont),
    KApp(List<JValue>, Env, List<JExpr>, Cont),
    KCase(Env, (JVarRef, JExpr), (JVarRef, JExpr), Cont),
    KCallCC(Cont),
}

macro_rules! kwrap {
    ($body:ident($($arg:expr),*)) => { Cont(Leak::new(ContBody::$body($($arg),*))) };
}

// Cont constructor functions
pub fn kret() -> Cont {
    Cont(Leak::new(ContBody::KRet))
}

pub fn kif(env: Env, et: JExpr, ef: JExpr, k: Cont) -> Cont {
    kwrap!(KIf(env, et, ef, k))
}

pub fn kapp(v: List<JValue>, env: Env, e: List<JExpr>, k: Cont) -> Cont {
    kwrap!(KApp(v, env, e, k))
}

pub fn kcase(env: Env, inl: (JVarRef, JExpr), inr: (JVarRef, JExpr), k: Cont) -> Cont {
    kwrap!(KCase(env, inl, inr, k))
}

pub fn kcallcc(k: Cont) -> Cont {
    kwrap!(KCallCC(k))
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

        let Cek(orig_body, env, orig_k) = self;

        // Rules from 6-6 plus lambda/closure rules from 6-11
        match (*orig_body, *orig_k) {
            // Rules 1..5 from 6-6
            (JVarRef(x), _k) => match env.get(x) {
                Some(v) => Cek(jval(v), Env::EMPTY, orig_k),
                None => Cek(str_to_abort("missing var in env"), env, orig_k),
            },
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

            // 13-3 rule 3 apply on JCont
            // has to come before regular apply rule
            (JVal(v_), KApp(v, _, _, _)) if v.head().map(JValue::is_j_cont).unwrap_or(false) => {
                let kp = v.head().unwrap().unwrap_j_cont();
                Cek(jval(v_), Env::EMPTY, kp)
            }

            // Combination of two rules (6-6 rule 7 and 6-11 rule 2)
            // Apply where all parameters have been evaluated to values
            (JVal(vn), KApp(v, _envp, _e, k)) => {
                let v = cons(vn, v);

                if let JClosure(_f, xs, ebody, envp) = v.last() {
                    // Closure eval (rule 2) from 6-11
                    // apply where we are applying to a closure
                    match Env::from_func_apply(envp, xs, v) {
                        Some(env) => Cek(ebody, env, k),
                        None => Cek(str_to_abort("Called func with wrong num of args"), env, k),
                    }
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

            // Abort case
            (JAbort(e), _k) => Cek(e, env, kret()),

            // 13-3 callcc related rules
            (JCallCC(e), _k) => Cek(e, env, kcallcc(orig_k)),
            (JVal(v), KCallCC(k)) => {
                Cek(jval(JCont(k)), Env::EMPTY, kapp([v].into(), Env::EMPTY, [].into(), k))
            }

            _ => {
                self.print_debug();
                Cek(str_to_abort("CEK hit bottom case"), env, orig_k)
            }
        }
    }
}

// Delta expects a list in reverse order, because of the cek machine
// rule 5 reverse-order trick
fn run_delta(list: List<JValue>) -> JExpr {
    // Lazy implementation using vec to reverse the list and get clean match code
    let mut vec = list.to_vec();
    vec.reverse();
    run_delta_slice(vec.as_slice())
}

fn run_delta_slice(vals: &[JValue]) -> JExpr {
    use JValue::*;

    let v = match vals[..] {
        [JPlus, JNum(a), JNum(b)] => JNum(a + b),
        [JMinus, JNum(a), JNum(b)] => JNum(a - b),
        [JMult, JNum(a), JNum(b)] => JNum(a * b),
        [JDiv, _, JNum(0)] => return str_to_abort("divide by zero"),
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

        [JNumberQ, x] => JBool(x.is_j_num()),
        [JBoxQ, x] => JBool(x.is_j_sigma()),
        [JBooleanQ, x] => JBool(x.is_j_bool()),
        [JPairQ, x] => JBool(x.is_j_pair()),
        [JUnitQ, x] => JBool(x.is_j_unit()),
        [JInlQ, x] => JBool(x.is_j_inl()),
        [JInrQ, x] => JBool(x.is_j_inr()),
        [JContinuationQ, x] => JBool(x.is_j_cont()),
        [JFunctionQ, x] => JBool(x.is_j_closure()),
        [JPrimitiveQ, x] => {
            // Free expr? (and the subexpr if its an abort)
            let expr = run_delta_slice(&[JPrimitiveArity, x]);
            let b = expr.is_j_val();
            JBool(b)
        }
        [JFunctionArity, JClosure(_, params, _, _)] => JNum(params.len() as i32),
        [JPrimitiveArity, x] => JNum(match x {
            JPlus | JMinus | JMult | JDiv | JLtEq | JLt | JEq | JGt | JGtEq | JPairOp | JStrEq => 2,
            JInlOp | JInrOp | JFst | JSnd | JBox | JUnbox | JSetBox | JNumberQ | JBoxQ
            | JBooleanQ | JPairQ | JUnitQ | JInlQ | JInrQ | JContinuationQ | JFunctionQ
            | JPrimitiveQ | JFunctionArity | JPrimitiveArity => 1,
            _ => return str_to_abort("primitive-arity called on non-primitive"),
        }),
        _ => {
            println!("delta couldn't handle: {:?}", vals);
            return str_to_abort("delta hit bottom case");
        }
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

    pub fn get(self, var_ref: JVarRef) -> Option<JValue> {
        let mut curr = *self;

        while let Some(((x, v), next)) = curr.head_tail() {
            if *x == var_ref {
                return Some(v.get());
            }
            curr = next;
        }

        println!("No var {} in environment", var_ref);
        None
    }

    // Generate an env for a closure body
    // Expects v to be in reverse and contain the closure at the end, so no manipulation of v
    // is needed in Cek::step
    pub fn from_func_apply(mut env: Env, x: List<JVarRef>, v: List<JValue>) -> Option<Env> {
        // Lazy impl using vecs for cleaner code
        let x = x.to_vec();
        let mut v = v.to_vec();
        v.pop();
        v.reverse();

        // Parameter len doesnt equal argument count
        if x.len() != v.len() {
            None
        } else {
            for (x, v) in x.iter().zip(v.iter()) {
                env = env.cons((*x, *v));
            }
            Some(env)
        }
    }
}
