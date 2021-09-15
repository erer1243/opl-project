-- For SExpr overloading
{-# LANGUAGE OverloadedStrings, OverloadedLists, TypeFamilies #-}

-- For SExpr overloading
import GHC.Exts (IsList(..))
import Data.String (IsString(..))

data JExpr = JVal JValue
           | JIf JExpr JExpr JExpr
           | JApply JExpr [JExpr]
           deriving (Show, Eq)

data JValue = JNum Integer
            | JBool Bool
            | JPlus | JMinus | JMult | JDiv | JLtEq | JLt | JEq | JGt | JGtEq
            deriving (Show, Eq)

data Context = CHole
             | CIf Context JExpr JExpr
             | CApp [JValue] Context [JExpr]
             deriving (Show, Eq)

data SExpr = SESym String | SENum Integer | SEList [SExpr] deriving (Show, Eq)

pp :: JExpr -> String
pp (JVal val) = case val of
    JNum n -> show n
    JBool b -> show b
    JPlus -> "+"
    JMinus -> "-"
    JMult -> "*"
    JDiv -> "/"
    JEq -> "="
    JLt -> "<"
    JGt -> ">"
    JLtEq -> "<="
    JGtEq -> ">="
pp (JIf cond e1 e2) = "(if " ++ pp cond ++ " " ++ pp e1 ++ " " ++ pp e2 ++ ")"
pp (JApply head args) = "(" ++ pp head ++ " " ++ printedArgs ++ ")"
  where
    printedArgs = unwords $ map pp args

interp :: JExpr -> JValue
interp (JVal v) = v
interp (JIf ec et ef) = if interp ec == JBool False then interp ef else interp et
interp (JApply efn eargs) = delta vfn vargs
  where
    vfn = interp efn
    vargs = map interp eargs

delta :: JValue -> [JValue] -> JValue
delta JPlus [JNum a, JNum b] = JNum (a + b)
delta JMinus [JNum a, JNum b] = JNum (a - b)
delta JMult [JNum a, JNum b] = JNum (a * b)
delta JDiv [JNum a, JNum b] = JNum (a `div` b)
delta JLtEq [JNum a, JNum b] = JBool (a <= b)
delta JLt [JNum a, JNum b] = JBool (a < b)
delta JEq [JNum a, JNum b] = JBool (a == b)
delta JGt [JNum a, JNum b] = JBool (a > b)
delta JGtEq [JNum a, JNum b] = JBool (a >= b)
delta _ _ = error "Bad JApply"

plug :: Context -> JExpr -> JExpr
plug CHole e = e
plug (CIf ctx et ef) e = JIf (plug ctx e) et ef
plug (CApp before ctx after) e = case before of
    -- The context is the prim
    [] -> JApply (plug ctx e) after
    -- The context is an argument to the prim
    before ->
        let (prim:argsBefore) = map JVal before
            args = argsBefore ++ plug ctx e : after
        in JApply prim args

fr :: JExpr -> Maybe (Context, JExpr)
fr (JVal _ ) = Nothing
fr e@(JIf ec et ef) = case fr ec of
    Nothing -> Just (CHole, e)
    Just (ctx, rdx) -> Just (CIf ctx et ef, rdx)
fr e@(JApply prim args) =
    case span isJVal applyList of
        (v, []) -> Just (CHole, e)
        (v, e0:em) ->
            -- The above branch guarantees all elements in v are JVal
            let vals = map unwrapJVal v
                Just (ctx, rdx) = fr e0
            in Just (CApp vals ctx em, rdx)
  where
    applyList = prim : args
    isJVal (JVal _) = True
    isJVal _ = False

smallStepInterp :: JExpr -> JValue
smallStepInterp e = case fr e of
    -- fr says that e is a JVal, so it is safe to unwrap it
    Nothing -> unwrapJVal e
    Just (ctx, rdx) -> smallStepInterp $ plug ctx $ step rdx

-- Usage of fr in smallStepInterp guarantees all parts
-- of each JExpr passed to step are a JVal
step :: JExpr -> JExpr
step (JIf (JVal (JBool False)) _ ef) = ef
step (JIf (JVal _) et _) = et
step (JApply p v) = JVal $ delta (unwrapJVal p) (map unwrapJVal v)
step _ = error "Bad step"

desugar :: SExpr -> JExpr
desugar (SENum n) = JVal $ JNum n
desugar (SEList l) = case l of
    -- +/* base cases
    [SESym "+"] -> toJNum 0
    [SESym "*"] -> toJNum 1
    -- +/* recursive cases
    (plus@(SESym "+"):head:tail) -> JApply (JVal JPlus) [desugar head,
                                                         desugar $ SEList $ plus : tail]
    (mult@(SESym "*"):head:tail) -> JApply (JVal JMult) [desugar head,
                                                         desugar $ SEList $ mult : tail]
    -- negation
    [SESym "-", SENum n] -> toJNum $ negate n
    -- other prims
    [sym@(SESym _), SENum lhs, SENum rhs] -> JApply (desugar sym) [toJNum lhs, toJNum rhs]
    [SESym "if", ec, et, ef] -> JIf (desugar ec) (desugar et) (desugar ef)
    l -> error $ "bad SEList " ++ show l
  where
    toJNum = JVal . JNum
desugar (SESym s) = JVal $ case s of
    "+" -> JPlus
    "-" -> JMinus
    "*" -> JMult
    "/" -> JDiv
    "=" -> JEq
    "<" -> JLt
    ">" -> JGt
    "<=" -> JLtEq
    ">=" -> JGtEq
    "true" -> JBool True
    "false" -> JBool False
    s -> error $ "bad SESym " ++ s

-- Helper function that unwraps a JValue from a JExpr JVal variant
-- In a couple places, we are guaranteed that a JExpr is a JVal
-- and this is useful. I believe I wrote the code in such a way that the
-- error branch is impossible to hit, even given a malformed JExpr.
unwrapJVal :: JExpr -> JValue
unwrapJVal (JVal v) = v
unwrapJVal e = error $ "unwrapJVal " ++ show e

checkJExprBig :: JExpr -> JValue -> Bool
checkJExprBig expr ans = interp expr == ans

checkJExprSmall :: JExpr -> JValue -> Bool
checkJExprSmall expr ans = smallStepInterp expr == ans

checkSExpr :: SExpr -> JValue -> Bool
checkSExpr expr ans = checkJExprBig jExpr ans && checkJExprSmall jExpr ans
  where
    jExpr = desugar expr

-- [(program, expected_answer)]
tests :: [(SExpr, JValue)]
tests = [ (1, JNum 1)
        , (["+", 1, 2, 3, 4], JNum 10)
        , (["*", 1, 2, 3, 4], JNum 24)
        , (["-", 3, 2], JNum 1)
        , (["/", 4, 2], JNum 2)
        , (["=", 0, 1], JBool False)
        , (["<", 0, 1], JBool True)
        , ([">", 0, 1], JBool False)
        , (["<=", 1, 1], JBool True)
        , ([">=", 0, 1], JBool False)
        , (["if", ["<", 0, 1], 1, 0], JNum 1)
        , (["if", "false", 5, "<="], JLtEq)
        ]

runTests :: IO ()
runTests = do
    let testResults = map (uncurry checkSExpr) tests
    let numSuccesses = length $ filter id testResults
    let numFailures = length tests - numSuccesses
    putStrLn $ show numSuccesses ++ " successes and " ++ show numFailures ++ " failures"

main :: IO ()
main = runTests

-- Enable conversion from number literals into SENum
-- Only fromInteger and negate are needed so the rest is left undefined
instance Num SExpr where
    fromInteger = SENum
    negate (SENum n) = SENum (negate n)
    negate _ = undefined
    (+) = undefined
    (*) = undefined
    abs = undefined
    signum = undefined

-- Enable conversion from string literals into SESym by OverloadedStrings
instance IsString SExpr where
    fromString = SESym

-- Enable conversion from list literals into SEList by OverloadedLists
-- Only fromList is needed so the rest is left broken
instance IsList SExpr where
    type Item SExpr = SExpr
    fromList = SEList
    toList = undefined
