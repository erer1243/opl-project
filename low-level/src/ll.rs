// #![allow(dead_code, unused_imports, unused_variables)]

// mod util;

use derive_more::{Deref, IsVariant, Unwrap};
use std::{
    cell::Cell,
    collections::VecDeque,
    mem::{align_of, size_of},
};
// pub use util::*;

// JExpr pointer wrapper type
#[derive(Copy, Clone, Deref, Debug, PartialEq, Eq)]
#[deref(forward)]
pub struct JExpr(Gc<JExprBody>);

// Types from page 9-2
#[derive(Copy, Clone, Debug, PartialEq, Eq, Unwrap, IsVariant)]
pub enum JExprBody {
    JVal(JValue),
    JIf(JExpr, JExpr, JExpr),
    JApply(JExpr, GcList<JExprBody>),
    JVarRef(JVarRef),
    JCase(JExpr, (JVarRef, JExpr), (JVarRef, JExpr)),
    JAbort(JExpr),
    JCallCC(JExpr),
}

pub type JVarRef = &'static str;

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

    JLambda(JVarRef, GcList<JVarRef>, JExpr),

    JUnit,
    JPair(Gc<JValue>, Gc<JValue>),
    JInl(Gc<JValue>),
    JInr(Gc<JValue>),
    JPairOp,
    JInlOp,
    JInrOp,
    JFst,
    JSnd,
    JString(JVarRef),
    JStrEq,

    JSigma(Gc<JValue>),
    JBox,
    JUnbox,
    JSetBox,

    // Closure type used in the CEK machine
    // This should never be used anywhere outside of Cek::step
    JClosure(JVarRef, GcList<JVarRef>, JExpr, Env),

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

macro_rules! jexpr {
    ($($fs:ident)*; $body:ident( $($args:expr),* )) => {{
        let (jb, gc) = mm().malloc(AllocTag::JExpr);
        let jb = jb as *mut JExprBody;
        if gc { $($fs.follow(); )* }
        unsafe { jb.write(JExprBody::$body($($args),*)); }
        JExpr(Gc(jb))
    }};
}

macro_rules! jvalue {
    ($($fs:ident)*; $val:expr) => {{
        let (jv, gc) = mm().malloc(AllocTag::JValue);
        let jv = jv as *mut JValue;
        if gc { $($fs.follow(); )* }
        unsafe { jv.write($val); }
        Gc(jv)
    }};
}

macro_rules! cont {
    ($($fs:ident)*; $body:ident( $($args:expr),* )) => {{
        let (cb, gc) = mm().malloc(AllocTag::Cont);
        let cb = cb as *mut ContBody;
        if gc { $($fs.follow(); )* }
        unsafe { cb.write(ContBody::$body($($args),*)); }
        Cont(Gc(cb))
    }};

    ($($fs:ident)*; KRet) => {{
        let (cb, gc) = mm().malloc(AllocTag::Cont);
        let cb = cb as *mut ContBody;
        if gc { $($fs.follow(); )* }
        unsafe { cb.write(ContBody::KRet); }
        Cont(Gc(cb))
    }}
}

macro_rules! abort_str {
    ($msg:expr) => {{
        let mut msg = jexpr!(; JVal(JValue::JString($msg)));
        jexpr!(msg; JAbort(msg))
    }}
}

macro_rules! follows {
    ($($fs:expr)*) => {{
        $($fs.follow();)*
    }}
}

// JValue gc allocated constructor
pub fn jvalue_gc(mut v: JValue) -> Gc<JValue> {
    jvalue!(v; v)
}

pub fn jexprs_to_gclist(exprs: &[JExpr]) -> GcList<JExprBody> {
    exprs.iter().rfold(GcList::EMPTY, |es, &e| es.cons(e.0))
}

pub fn jvarrefs_to_gclist(jvrs: &[JVarRef]) -> GcList<JVarRef> {
    let gc_jvrs: Vec<Gc<JVarRef>> = jvrs
        .iter()
        .map(|&jvr| {
            let (jvr_ptr, _) = mm().malloc(AllocTag::JVarRef);
            let jvr_ptr = jvr_ptr as *mut JVarRef;
            unsafe {
                jvr_ptr.write(jvr);
            }
            Gc(jvr_ptr)
        })
        .collect();

    gc_jvrs.into_iter().rfold(GcList::EMPTY, |jvrs, jvr| jvrs.cons(jvr))
}

// JExpr constructor functions
pub fn jif(mut ec: JExpr, mut et: JExpr, mut ef: JExpr) -> JExpr {
    jexpr!(ec et ef; JIf(ec, et, ef))
}

pub fn japply(mut e0: JExpr, mut em: GcList<JExprBody>) -> JExpr {
    jexpr!(e0 em; JApply(e0, em))
}

pub fn jval(mut v: JValue) -> JExpr {
    jexpr!(v; JVal(v))
}

pub fn jvarref(vr: JVarRef) -> JExpr {
    jexpr!(; JVarRef(vr))
}

pub fn jcase(mut e: JExpr, inl: (JVarRef, JExpr), inr: (JVarRef, JExpr)) -> JExpr {
    let (xl, mut el) = inl;
    let (xr, mut er) = inr;
    jexpr!(e el er; JCase(e, (xl, el), (xr, er)))
}

pub fn jabort(mut e: JExpr) -> JExpr {
    jexpr!(e; JAbort(e))
}

pub fn jcallcc(mut e: JExpr) -> JExpr {
    jexpr!(e; JCallCC(e))
}

// pub fn jabort_str(s: &'static str) -> JExpr {
//     jabort(jval(JValue::JString(s)))
// }

// Continuation pointer wrapper type
#[derive(Copy, Clone, Deref, PartialEq, Eq, Debug)]
#[deref(forward)]
pub struct Cont(Gc<ContBody>);

// K ::= KRet | (KIf e e K) | (KApp (v..) (e..) K)
// Aka Continuation
#[derive(Clone, Copy, IsVariant, PartialEq, Eq, Debug)]
pub enum ContBody {
    KRet,
    KIf(Env, JExpr, JExpr, Cont),
    KApp(GcList<JValue>, Env, GcList<JExprBody>, Cont),
    KCase(Env, (JVarRef, JExpr), (JVarRef, JExpr), Cont),
    KCallCC(Cont),
}

// macro_rules! kwrap {
//     ($body:ident($($arg:expr),*)) => { Cont(mm().cont(ContBody::$body($($arg),*))) };
// }

// Cont constructor functions
pub fn kret() -> Cont {
    cont!(; KRet)
    // Cont(mm().cont(cek, ContBody::KRet))
}

// pub fn kif(mut env: Env, mut et: JExpr, mut ef: JExpr, mut k: Cont) -> Cont {
//     cont!(env et ef k; KIf(env, et, ef, k))
// }

// pub fn kapp(mut v: GcList<JValue>, mut env: Env, mut e: GcList<JExpr>, mut k: Cont) -> Cont {
//     cont!(v env e k; KApp(v, env, e, k))
// }

// pub fn kcase(mut env: Env, inl: (JVarRef, JExpr), inr: (JVarRef, JExpr), mut k: Cont) -> Cont {
//     let (xl, mut el) = inl;
//     let (xr, mut er) = inr;
//     cont!(env el er k; KCase(env, (xl, el), (xr, er), k))
// }

// pub fn kcallcc(mut k: Cont) -> Cont {
//     cont!(k; KCallCC(k))
// }

// const MEM_MANAGER_SIZE: usize = 5_000_000_000;
const MEM_MANAGER_SIZE: usize = 30_000_000;
// global stop and copy mem manager
static mut MEM_MANAGER: Option<MemManager> = None;
// global Cek state that the mem manager uses for the root set when doing gc
static mut MM_CEK: Option<Cek> = None;

// answer holder mem manager
// expected test answer objects go into this so they don't get garbage collected
// by the normal global memory manager
static mut PERM_MEM_MANAGER: Option<MemManager> = None;

fn mm() -> &'static mut MemManager {
    unsafe {
        if MEM_MANAGER.is_none() {
            MEM_MANAGER = Some(MemManager::new(MEM_MANAGER_SIZE));
        }
        MEM_MANAGER.as_mut().unwrap()
    }
}

fn set_mm_cek(cek: Cek) {
    unsafe {
        MM_CEK = Some(cek);
    }
}

fn mm_cek_follow() {
    unsafe {
        if let Some(mut cek) = MM_CEK {
            cek.0.follow();
            cek.1.follow();
            cek.2.follow();
            set_mm_cek(cek);
        }
    }
}

pub fn drop_mm() {
    unsafe {
        MM_CEK = None;
        MEM_MANAGER = None;
    }
}

pub fn switch_mm() {
    unsafe {
        PERM_MEM_MANAGER = MEM_MANAGER.take();
    }
}

// Cek machine
// st = <e, k>
#[derive(Clone, Copy)]
pub struct Cek(JExpr, Env, Cont);

impl Cek {
    pub fn evaluate(e: JExpr) -> JValue {
        let mut cek = Cek(e, Env::EMPTY, kret());

        while !cek.is_finished() {
            set_mm_cek(cek);
            cek = cek.step();
        }

        cek.0.unwrap_j_val()
    }

    fn is_finished(&self) -> bool {
        self.0.is_j_val() && self.2.is_k_ret()
    }

    // Aka the arrow function |-> from lecture 4
    pub fn step(self) -> Cek {
        use ContBody::*;
        use JExprBody::*;
        use JValue::*;

        let Cek(mut cek_c, mut cek_e, mut cek_k) = self;
        follows!(cek_c cek_e cek_k);

        macro_rules! jexpr_ {
            ($($fs:ident)*; $body:ident( $($args:expr),* )) => {
                jexpr!(cek_c cek_e cek_k $($fs)*; $body($($args),*))
            };
        }

        macro_rules! cont_ {
            ($($fs:ident)*; $body:ident( $($args:expr),* )) => {
                cont!(cek_c cek_e cek_k $($fs)*; $body($($args),*))
            };
            ($($fs:ident)*; KRet) => { cont!(cek_c cek_e cek_k $($fs)*; KRet) };
        }

        macro_rules! jvalue_ {
            ($($fs:ident)*; $val:expr) => {
                jvalue!(cek_k cek_e cek_k $($fs)*; $val)
            }
        }

        macro_rules! abort_str_ {
            ($msg:expr) => {{
                let mut msg = jexpr_!(; JVal(JValue::JString($msg)));
                jexpr_!(msg; JAbort(msg))
            }};
        }

        // Rules from 6-6 plus lambda/closure rules from 6-11
        match (*cek_c, *cek_k) {
            // Rules 1..5 from 6-6
            (JVarRef(x), _k) => match cek_e.get(x) {
                Some(mut v) => Cek(jexpr_!(v; JVal(v)), Env::EMPTY, cek_k),
                None => Cek(abort_str_!("missing var in env"), cek_e, cek_k),
            },

            (JIf(mut ec, mut et, mut ef), _k) => {
                let k = cont_!(ec et ef; KIf(cek_e, et, ef, cek_k));
                Cek(ec, cek_e, k)
            }

            (JVal(JBool(false)), KIf(envp, _et, ef, k)) => Cek(ef, envp, k),

            (JVal(_), KIf(envp, et, _ef, k)) => Cek(et, envp, k),

            (JApply(mut e0, mut em), _) => {
                let k = cont_!(e0 em; KApp(GcList::EMPTY, cek_e, em, cek_k));
                Cek(e0, cek_e, k)
            }

            // Lambda to closure (rule 1) from 6-11
            // Updated to support closures with recurse name, 8-2,8-3
            (JVal(JLambda(f, mut xs, mut ebody)), _k) => {
                let mut envp = cek_e.cons((f, JValue::JNum(0)));
                follows!(cek_c cek_e cek_k xs ebody);
                let mut clos = JClosure(f, xs, ebody, envp);
                envp.update((f, clos));
                let clos_jv = jexpr_!(clos; JVal(clos));
                Cek(clos_jv, cek_e, cek_k)
            }

            // Rule 6 from 6-6
            // Apply where some parameters need to be evaluated
            (JVal(mut v1), KApp(mut v, mut envp, mut e, mut k)) if !e.is_empty() => {
                // Reverse-order trick from lecture 4
                // Values in v are stored in reverse order compared with e
                let jv = jvalue_!(v1 v envp e k; v1);
                let mut v = v.cons(jv);
                let (mut e0, mut em) = e.head_tail().unwrap();
                let k = cont_!(v e0 em envp k; KApp(v, envp, em, k));
                Cek(JExpr(e0), envp, k)
            }

            // 13-3 rule 3 apply on JCont
            // has to come before regular apply rule
            (JVal(_), KApp(vs, _, _, _))
                if vs.len() == 1 && vs.head().map(|h| h.is_j_cont()).unwrap_or(false) =>
            {
                let kp = vs.head().unwrap().unwrap_j_cont();
                Cek(cek_c, Env::EMPTY, kp)
            }

            // Combination of two rules (6-6 rule 7 and 6-11 rule 2)
            // Apply where all parameters have been evaluated to values
            (JVal(mut vn), KApp(mut v, _envp, _e, mut k)) => {
                let jv = jvalue_!(vn v k; vn);
                let v = v.cons(jv);

                if let JClosure(_f, xs, mut ebody, envp) = *v.last() {
                    // Closure eval (rule 2) from 6-11
                    // apply where we are applying to a closure
                    let env_res = Env::from_func_apply(envp, xs, v);
                    follows!(ebody k);
                    match env_res {
                        Some(env) => Cek(ebody, env, k),
                        None => {
                            let e = abort_str_!("Called func with wrong num of args");
                            follows!(k);
                            Cek(e, cek_e, k)
                        }
                    }
                } else {
                    // Rule 7 from 6-6
                    // Apply where we are applying to a prim
                    let delta_e = run_delta(v);
                    follows!(k);
                    Cek(delta_e, Env::EMPTY, k)
                }
            }

            // Case into kcase continuation, invented from 9-3
            (JCase(e, inl, inr), _k) => {
                let (xl, mut el) = inl;
                let (xr, mut er) = inr;
                let k = cont_!(el er; KCase(cek_e, (xl, el), (xr, er), cek_k));
                Cek(e, cek_e, k)
            }

            // Case branch rules, invented from 9-3
            (JVal(JInl(v)), KCase(envp, (xl, mut el), _inr, mut k)) => {
                let env = envp.cons((xl, *v));
                follows!(k el cek_e cek_c cek_k);
                Cek(el, env, k)
            }

            (JVal(JInr(v)), KCase(envp, _inl, (xr, mut er), mut k)) => {
                let env = envp.cons((xr, *v));
                follows!(k er cek_e cek_c cek_k);
                Cek(er, env, k)
            }

            // Abort case
            (JAbort(mut e), _k) => {
                let k = cont_!(e; KRet);
                Cek(e, cek_e, k)
            }

            // 13-3 callcc related rules
            (JCallCC(mut e), _k) => {
                let k = cont_!(e; KCallCC(cek_k));
                Cek(e, cek_e, k)
            }

            (JVal(mut v), KCallCC(mut k)) => {
                let mut e = jexpr_!(v k; JVal(JCont(k)));
                let mut gc_v = jvalue_!(e v k; v);
                let mut vs = GcList::EMPTY.cons(gc_v);
                follows!(e k gc_v vs);
                let k = cont_!(e k vs; KApp(vs, Env::EMPTY, GcList::EMPTY, k));
                Cek(e, Env::EMPTY, k)
            }

            _ => Cek(abort_str_!("CEK hit bottom case"), cek_e, cek_k),
        }
    }
}

// Delta expects a list in reverse order, because of the cek machine
// rule 5 reverse-order trick
fn run_delta(list: GcList<JValue>) -> JExpr {
    // Lazy implementation using vec to reverse the list and get clean match code
    let mut vec = list.to_vec();
    vec.reverse();
    let vec: Vec<JValue> = vec.iter().map(|gc_jv| **gc_jv).collect();
    run_delta_slice(vec.as_slice())
}

fn run_delta_slice(vals: &[JValue]) -> JExpr {
    use JValue::*;

    let mut v = match vals[..] {
        [JPlus, JNum(a), JNum(b)] => JNum(a + b),
        [JMinus, JNum(a), JNum(b)] => JNum(a - b),
        [JMult, JNum(a), JNum(b)] => JNum(a * b),
        [JDiv, _, JNum(0)] => return abort_str!("divide by zero"),
        [JDiv, JNum(a), JNum(b)] => JNum(a / b),
        [JLtEq, JNum(a), JNum(b)] => JBool(a <= b),
        [JLt, JNum(a), JNum(b)] => JBool(a < b),
        [JEq, JNum(a), JNum(b)] => JBool(a == b),
        [JGt, JNum(a), JNum(b)] => JBool(a > b),
        [JGtEq, JNum(a), JNum(b)] => JBool(a >= b),

        [JInlOp, mut v] => JInl(jvalue!(v; v)),
        [JInrOp, mut v] => JInr(jvalue!(v; v)),

        [JPairOp, mut vl, mut vr] => {
            let mut vl = jvalue!(vl vr; vl);
            let vr = jvalue!(vl vr; vr);
            JPair(vl, vr)
        }
        [JFst, JPair(vl, _)] => *vl,
        [JSnd, JPair(_, vr)] => *vr,

        [JStrEq, JString(a), JString(b)] => JBool(a == b),

        [JBox, mut v] => JSigma(jvalue!(v; v)),
        [JUnbox, JSigma(l)] => *l,
        [JSetBox, JSigma(mut l), v] => {
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
            JPlus | JMinus | JMult | JDiv | JLtEq | JLt | JEq | JGt | JGtEq | JPairOp | JStrEq
            | JSetBox => 2,
            JInlOp | JInrOp | JFst | JSnd | JBox | JUnbox | JNumberQ | JBoxQ | JBooleanQ
            | JPairQ | JUnitQ | JInlQ | JInrQ | JContinuationQ | JFunctionQ | JPrimitiveQ
            | JFunctionArity | JPrimitiveArity => 1,
            _ => return abort_str!("primitive-arity called on non-primitive"),
        }),
        _ => return abort_str!("delta hit bottom case"),
    };

    jexpr!(v; JVal(v))
}

#[derive(Copy, Clone, Deref, Debug, PartialEq, Eq)]
pub struct Env(GcList<EnvPair>);
pub type EnvPair = (JVarRef, Cell<JValue>);

impl Env {
    const EMPTY: Env = Env(GcList::EMPTY);

    fn cons(mut self, mut pair: (JVarRef, JValue)) -> Env {
        let (ep, gc) = mm().malloc(AllocTag::EnvPair);
        let ep = ep as *mut EnvPair;
        if gc {
            self.follow();
            pair.1.follow();
        }
        unsafe {
            ep.write((pair.0, Cell::new(pair.1)));
        }
        let gc_ep = Gc(ep);
        Env(self.0.cons(gc_ep))
    }

    fn update(&mut self, (name, val): (JVarRef, JValue)) {
        let mut curr = **self;

        while let Some((pair, next)) = curr.head_tail() {
            let (x, v) = &*pair;
            if *x == name {
                v.set(val);
                break;
            }
            curr = next;
        }
    }

    fn get(self, var_ref: JVarRef) -> Option<JValue> {
        let mut curr = *self;

        while let Some((pair, next)) = curr.head_tail() {
            let (x, v) = &*pair;
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
    fn from_func_apply(mut env: Env, x: GcList<JVarRef>, v: GcList<JValue>) -> Option<Env> {
        // Lazy impl using vecs for cleaner code
        let x = x.to_vec();
        let mut v = v.to_vec();
        v.pop();
        v.reverse();

        // Parameter len doesnt equal argument count
        if x.len() != v.len() {
            None
        } else {
            for (mut x, mut v) in x.into_iter().zip(v.into_iter()) {
                follows!(x v);
                env = env.cons((*x, *v));
            }
            Some(env)
        }
    }
}

struct MemManager {
    size: usize,
    mem: Box<[u8]>,
    half: bool,
    free_index: usize,
    doing_gc: bool,
}

impl MemManager {
    fn new(size: usize) -> MemManager {
        // println!("{:.2} gigabytes allocated as gc'd memory", (size as f64 / 1_000_000_000f64));

        // pad memory with some extra bytes to avoid ub described in std::ptr docs
        let size = size + 300;

        MemManager {
            size,
            mem: vec![0u8; size * 2].into(),
            half: false,
            free_index: 0,
            doing_gc: false,
        }
    }

    // Run stop and copy gc
    fn gc(&mut self) {
        if self.doing_gc {
            panic!("gc during gc, ran out of memory");
        }
        self.doing_gc = true;

        // switch to other buffer
        let old_free = self.free_index;
        self.free_index = 0;
        self.half = !self.half;

        // to-be-moved queue
        let mut q: VecDeque<*mut u8> = VecDeque::new();

        // to-be-updated stack
        let mut new_objs: Vec<*mut u8> = Vec::new();

        // add cek machine to queue
        let Cek(c, e, k) = unsafe { MM_CEK.expect("Cannot gc because Cek not running") };
        q.push_back((c.0).0.cast());
        q.push_back((k.0).0.cast());
        if let Some(gc) = (e.0).0 {
            q.push_back(gc.0.cast())
        }

        // realloc the objects
        while let Some(ptr) = q.pop_front() {
            if let Some(new_ptr) = self.realloc_obj(ptr) {
                MemManager::get_child_ptrs(new_ptr, &mut q);
                new_objs.push(new_ptr);
            }
        }

        // update the objects' fields in place
        for ptr in new_objs {
            MemManager::follow_child_ptrs(ptr);
        }

        // update global cek
        mm_cek_follow();
        self.doing_gc = false;

        let free_mb = (old_free.saturating_sub(self.free_index)) as f64 / 1_000_000f64;
        println!("Performed gc, freed {:.02} mb", free_mb);
    }

    // copy a single object to new memory region during gc
    fn realloc_obj(&mut self, src: *mut u8) -> Option<*mut u8> {
        unsafe {
            let tag = MemManager::obj_tag(src);

            if tag == AllocTag::Forwarding {
                // Already reallocated, just return forwarded ptr
                // src.cast::<ForwardingPtr>().read().0

                // already reallocated, return none
                None
            } else {
                // Not reallocated yet, allocate space and setup forwarding ptr
                let tag_ptr = src.sub(1);
                let dst = self.malloc(tag).0;
                src.copy_to(dst, tag.size());
                tag_ptr.cast::<AllocTag>().write(AllocTag::Forwarding);
                src.cast::<ForwardingPtr>().write(ForwardingPtr(dst));
                Some(dst)
            }
        }
    }

    fn follow_child_ptrs(ptr: *mut u8) {
        unsafe {
            let tag = MemManager::obj_tag(ptr);
            match tag {
                AllocTag::JExpr => {
                    let ptr = ptr as *mut JExprBody;
                    let je = &mut *ptr;
                    match je {
                        JExprBody::JVal(v) => v.follow(),
                        JExprBody::JIf(a, b, c) => follows!(a b c),
                        JExprBody::JApply(a, b) => follows!(a b),
                        JExprBody::JVarRef(_) => (),
                        JExprBody::JCase(e, (_, l), (_, r)) => follows!(e l r),
                        JExprBody::JAbort(e) => e.follow(),
                        JExprBody::JCallCC(e) => e.follow(),
                    }
                }
                AllocTag::JValue => {
                    let jv = &mut *(ptr as *mut JValue);
                    jv.follow();
                }
                AllocTag::Cont => match &mut *(ptr as *mut ContBody) {
                    ContBody::KRet => (),
                    ContBody::KIf(a, b, c, d) => follows!(a b c d),
                    ContBody::KApp(a, b, c, d) => follows!(a b c d),
                    ContBody::KCase(e, (_, l), (_, r), k) => follows!(e l r k),
                    ContBody::KCallCC(k) => k.follow(),
                },
                AllocTag::GcCons => {
                    let gcc = &mut *(ptr as *mut GcCons<u8>);
                    follows!(gcc.data GcList(gcc.next));
                }
                AllocTag::EnvPair => {
                    let ep = &mut *(ptr as *mut EnvPair);
                    follows!(ep.1.get_mut())
                }
                AllocTag::JVarRef => (),
                AllocTag::Forwarding => (),
            }
        }
    }

    fn get_child_ptrs(ptr: *mut u8, vec: &mut VecDeque<*mut u8>) {
        macro_rules! add {
            () => {};
            ($itm:expr, $($rest:tt)*) => {{
                vec.push_back($itm.0.0 as *mut u8);
                add!($($rest)*);
            }};
            (@$itm:expr, $($rest:tt)*) => {{
                if !$itm.is_empty() {
                    vec.push_back($itm.0.unwrap().0.cast());
                }
                add!($($rest)*);
            }};
        }
        unsafe {
            let tag = MemManager::obj_tag(ptr);
            match tag {
                AllocTag::JExpr => match ptr.cast::<JExprBody>().read() {
                    JExprBody::JVal(v) => jvalue_ptrs(v, vec),
                    JExprBody::JIf(a, b, c) => add!(a, b, c,),
                    JExprBody::JApply(p, a) => add!(p, @a,),
                    JExprBody::JVarRef(_) => (),
                    JExprBody::JCase(e, (_, l), (_, r)) => add!(e, l, r,),
                    JExprBody::JAbort(e) => add!(e,),
                    JExprBody::JCallCC(e) => add!(e,),
                },
                AllocTag::JValue => jvalue_ptrs(ptr.cast::<JValue>().read(), vec),
                AllocTag::Cont => match ptr.cast::<ContBody>().read() {
                    ContBody::KRet => (),
                    ContBody::KIf(a, b, c, d) => add!(@a.0, b, c, d,),
                    ContBody::KApp(a, b, c, d) => add!(@a, @b.0, @c, d,),
                    ContBody::KCase(a, (_, b), (_, c), d) => add!(@a.0, b, c, d,),
                    ContBody::KCallCC(k) => add!(k,),
                },
                AllocTag::GcCons => {
                    let gcc = ptr.cast::<GcCons<u8>>().read();
                    let data = (gcc.data,);
                    let next = GcList(gcc.next);
                    add!(data, @next,);
                }
                AllocTag::EnvPair => {
                    let pair = ptr.cast::<EnvPair>().read();
                    jvalue_ptrs(pair.1.get(), vec);
                }
                AllocTag::Forwarding => (),
                AllocTag::JVarRef => (),
            }
        }

        fn jvalue_ptrs(jv: JValue, vec: &mut VecDeque<*mut u8>) {
            use JValue::*;
            match jv {
                JLambda(_, xs, e) => {
                    if !xs.is_empty() {
                        vec.push_back(xs.0.unwrap().0.cast());
                    }
                    vec.push_back(e.0 .0.cast());
                }
                JClosure(_, xs, e, env) => {
                    if !xs.is_empty() {
                        vec.push_back(xs.0.unwrap().0.cast());
                    }
                    vec.push_back(e.0 .0.cast());
                    if !env.0.is_empty() {
                        vec.push_back(env.0 .0.unwrap().0.cast());
                    }
                }
                JPair(l, r) => {
                    vec.push_back(l.0.cast());
                    vec.push_back(r.0.cast());
                }
                JInl(v) => {
                    vec.push_back(v.0.cast());
                }
                JInr(v) => {
                    vec.push_back(v.0.cast());
                }
                JSigma(v) => {
                    vec.push_back(v.0.cast());
                }
                JCont(k) => {
                    vec.push_back(k.0 .0.cast());
                }
                _ => (),
            }
        }
    }

    // Allocate space for a tag and its associated Cek type
    fn malloc(&mut self, tag: AllocTag) -> (*mut u8, bool) {
        unsafe {
            // calculate necessary pointers and alignment data
            let free_ptr = self.current_mem().add(self.free_index);
            let free_1 = free_ptr.add(1);
            let data_ptr = free_1.add(free_1.align_offset(tag.align()));
            let tag_ptr = data_ptr.sub(1) as *mut AllocTag;
            let next_free_ptr = data_ptr.add(tag.size());
            let needed_bytes = next_free_ptr as usize - free_ptr as usize;

            if self.have_free(needed_bytes) {
                // mark space as used
                self.free_index += needed_bytes;
                // write tag
                *tag_ptr = tag;
                // return data ptr and say gc didnt happen
                (data_ptr, false)
            } else {
                // no space, gc
                self.gc();
                // if still no space, we will never have enough
                assert!(self.have_free(needed_bytes), "MemManager ran out of memory");
                // malloc again, this time say that gc happened
                (self.malloc(tag).0, true)
            }
        }
    }

    fn have_free(&self, bytes: usize) -> bool {
        self.free_index + bytes < self.size
    }

    fn current_mem(&mut self) -> *mut u8 {
        if self.half {
            self.mem[0..self.size].as_mut_ptr()
        } else {
            self.mem[self.size..2 * self.size].as_mut_ptr()
        }
    }

    fn obj_tag<T>(ptr: *mut T) -> AllocTag {
        unsafe {
            let tag_ptr_p1 = ptr.cast::<AllocTag>();
            let tag_ptr = tag_ptr_p1.sub(1);
            *tag_ptr
        }
    }

    fn follow_forwarding_ptr<T>(data: *mut T) -> *mut T {
        match MemManager::obj_tag(data) {
            AllocTag::Forwarding => unsafe { data.cast::<ForwardingPtr>().read().0.cast() },
            _ => data,
        }
    }
}

#[derive(Copy, Clone)]
struct ForwardingPtr(*mut u8);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
enum AllocTag {
    Forwarding,
    JExpr,
    JValue,
    Cont,
    GcCons,
    EnvPair,
    JVarRef,
}

impl AllocTag {
    fn align(&self) -> usize {
        let natural_align = match self {
            AllocTag::JExpr => align_of::<JExprBody>(),
            AllocTag::JValue => align_of::<JValue>(),
            AllocTag::Cont => align_of::<ContBody>(),
            AllocTag::GcCons => align_of::<GcCons<()>>(),
            AllocTag::Forwarding => align_of::<ForwardingPtr>(),
            AllocTag::EnvPair => align_of::<EnvPair>(),
            AllocTag::JVarRef => align_of::<JVarRef>(),
        };
        natural_align.max(align_of::<ForwardingPtr>())
    }

    fn size(&self) -> usize {
        let natural_size = match self {
            AllocTag::JExpr => size_of::<JExprBody>(),
            AllocTag::JValue => size_of::<JValue>(),
            AllocTag::Cont => size_of::<ContBody>(),
            AllocTag::GcCons => size_of::<GcCons<()>>(),
            AllocTag::Forwarding => size_of::<ForwardingPtr>(),
            AllocTag::EnvPair => size_of::<EnvPair>(),
            AllocTag::JVarRef => size_of::<JVarRef>(),
        };
        natural_size.max(size_of::<ForwardingPtr>())
    }
}

pub struct Gc<T>(*mut T);

impl<T> Gc<T> {
    // takes a forwarding pointer and follows it to its new location
    fn follow(&mut self) -> bool {
        let new_ptr = MemManager::follow_forwarding_ptr(self.0);
        if std::ptr::eq(new_ptr, self.0) {
            false
        } else {
            self.0 = new_ptr;
            true
        }
    }

    fn set(&mut self, data: T) {
        unsafe {
            *self.0 = data;
        }
    }
}

impl JExpr {
    fn follow(&mut self) {
        self.0.follow();
    }
}

impl Cont {
    fn follow(&mut self) {
        self.0.follow();
    }
}

impl JValue {
    fn follow(&mut self) {
        use JValue::*;
        match self {
            JLambda(_, xs, e) => {
                xs.follow();
                e.follow();
            }
            JPair(l, r) => {
                l.follow();
                r.follow();
            }
            JInl(v) => {
                v.follow();
            }
            JInr(v) => {
                v.follow();
            }
            JSigma(v) => {
                v.follow();
            }
            JCont(k) => {
                k.follow();
            }
            JClosure(_, xs, e, env) => {
                xs.follow();
                e.follow();
                env.follow();
            }
            _ => (),
        }
    }
}

impl Env {
    fn follow(&mut self) {
        self.0.follow();
    }
}

impl<T> GcList<T> {
    fn follow(&mut self) {
        if let Some(l) = &mut self.0 {
            l.follow();
            let gcc = unsafe { &mut *l.0 };
            gcc.follow();
        }
    }
}

impl<T> GcCons<T> {
    fn follow(&mut self) {
        self.data.follow();
        if let Some(l) = &mut self.next {
            l.follow();
            let gcc = unsafe { &mut *l.0 };
            gcc.follow();
        }
    }
}

impl<T> std::ops::Deref for Gc<T> {
    type Target = T;
    fn deref(&self) -> &T {
        if MemManager::obj_tag(self.0) == AllocTag::Forwarding {
            unsafe {
                #[allow(mutable_transmutes)]
                let gc = std::mem::transmute::<_, &mut Self>(self);
                gc.follow();
            }
        }
        unsafe { &*self.0 }
    }
}

impl<T> Clone for Gc<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Gc<T> {}

impl<T: std::fmt::Debug> std::fmt::Debug for Gc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::ops::Deref;
        write!(f, "{:?}", self.deref())
    }
}

impl<T: PartialEq> PartialEq<Gc<T>> for Gc<T> {
    fn eq(&self, other: &Gc<T>) -> bool {
        use std::ops::Deref;
        self.deref().eq(other)
    }
}

impl<T: Eq> Eq for Gc<T> {}

pub type Link<T> = Option<Gc<GcCons<T>>>;

#[derive(PartialEq, Eq)]
pub struct GcList<T>(Link<T>);

#[derive(PartialEq, Eq)]
pub struct GcCons<T> {
    data: Gc<T>,
    next: Link<T>,
}

impl<T: std::fmt::Debug> GcList<T> {
    const EMPTY: GcList<T> = GcList(None);

    fn cons(mut self, mut data: Gc<T>) -> GcList<T> {
        let (cons, gc) = mm().malloc(AllocTag::GcCons);
        let cons_ptr = cons as *mut GcCons<T>;
        if gc {
            self.follow();
            data.follow();
        }
        let cons_body = GcCons {
            data,
            next: self.0,
        };
        unsafe {
            cons_ptr.write(cons_body);
        }
        GcList(Some(Gc(cons_ptr)))
    }

    fn head_tail(&self) -> Option<(Gc<T>, GcList<T>)> {
        match &self.0 {
            Some(cons) => Some((cons.data, GcList(cons.next))),
            None => None,
        }
    }

    fn head(&self) -> Option<Gc<T>> {
        self.head_tail().map(|(t, _)| t)
    }

    fn is_empty(self) -> bool {
        self.0.is_none()
    }

    fn len(mut self) -> usize {
        let mut n = 0;
        while let Some((_, next)) = self.head_tail() {
            n += 1;
            self = next;
        }
        n
    }

    fn to_vec(self) -> Vec<Gc<T>> {
        let mut vec = Vec::new();

        let mut curr = self.0;
        while let Some(node) = curr {
            vec.push(node.data);
            curr = node.next;
        }

        vec
    }

    fn last(self) -> Gc<T> {
        *self.to_vec().last().unwrap()
    }
}

impl<T> Clone for GcList<T> {
    fn clone(&self) -> Self {
        GcList(self.0)
    }
}

impl<T> Copy for GcList<T> {}

impl<T: std::fmt::Debug> std::fmt::Debug for GcList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.to_vec())
    }
}
