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
