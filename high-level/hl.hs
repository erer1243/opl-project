-- For SExpr overloading
{-# LANGUAGE OverloadedStrings, OverloadedLists, TypeFamilies #-}

-- For SExpr overloading
import GHC.Exts (IsList(..))
import Data.String (IsString(..))

import Data.List (intercalate)
import System.Process (callCommand)
import Control.Monad (forM_)

-- e ::= v | (e e..) | (if e e e)
data JExpr = JVal JValue
           | JIf JExpr JExpr JExpr
           | JApply JExpr [JExpr]
           deriving (Show, Eq)

-- v ::= number | boolean | prim
-- prim ::= + | * | / | - | <= | < | = | > | >=
-- prim is not a separate data structure in my implementation
data JValue = JNum Integer
            | JBool Bool
            | JPlus | JMinus | JMult | JDiv | JLtEq | JLt | JEq | JGt | JGtEq
            deriving (Show, Eq)

-- E ::= [] | (if E e e) | (v.. E e..)
data Context = CHole
             | CIf Context JExpr JExpr
             | CApp [JValue] Context [JExpr]
             deriving (Show, Eq)

-- se ::= empty | (cons se se) | string
-- I decided to implement SExpr this way because it allows me
-- to take advantage of list, string, and number literal overloading in ghc
-- to write SExprs like ["+", 1, 2]
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
    [SESym "+"] -> JVal $ JNum 0
    [SESym "*"] -> JVal $ JNum 1
    -- +/* recursive cases
    (plus@(SESym "+"):head:tail) -> JApply (JVal JPlus) [desugar head,
                                                         desugar $ SEList $ plus : tail]
    (mult@(SESym "*"):head:tail) -> JApply (JVal JMult) [desugar head,
                                                         desugar $ SEList $ mult : tail]
    -- negation
    [SESym "-", en] -> JApply (JVal JMult) [JVal (JNum (-1)), desugar en]
    -- if condition
    [SESym "if", ec, et, ef] -> JIf (desugar ec) (desugar et) (desugar ef)
    -- apply
    (sym@(SESym _):tail) -> JApply (desugar sym) (map desugar tail)
    l -> error $ "bad SEList " ++ show l
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
        , (["+", 5, ["-", ["+", 2, 3]]], JNum 0)
        , (["+", ["*", ["/", 9, 3], 10], ["-", 10]], JNum 20)
        ]

runTests :: IO ()
runTests = do
    putStrLn "Running tests in HL code:"
    let testResults = map (uncurry checkSExpr) tests
    let numSuccesses = length $ filter id testResults
    let numFailures = length tests - numSuccesses
    putStrLn $ show numSuccesses ++ " successes and " ++ show numFailures ++ " failures"

    putStrLn "Running tests in LL code:"
    forM_ tests runTestInLL

-- Converts a single JExpr to low level rust code.
jeToLL :: JExpr -> String
jeToLL (JVal v) = "jval(" ++ jvToLL v ++ ")"
jeToLL (JIf ec et ef) =
    let commaSeparatedArgs = intercalate ", " (map jeToLL [ec, et, ef])
    in "jif(" ++ commaSeparatedArgs ++ ")"
jeToLL (JApply p args) =
    let commaSeparatedArgs = intercalate ", " $ map jeToLL args
    in "japply(" ++ jeToLL p ++ ", [" ++ commaSeparatedArgs ++ "])"

-- Converts a single JValue to low level rust code.
jvToLL :: JValue -> String
jvToLL v = "JValue::" ++ case v of
    JNum n -> "JNum(" ++ show n ++ ")"
    JBool b -> "JBool(" ++ (if b then "true" else "false") ++ ")"
    JPlus -> "JPlus"
    JMinus -> "JMinus"
    JMult -> "JMult"
    JDiv -> "JDiv"
    JLtEq -> "JLtEq"
    JLt -> "JLt"
    JEq -> "JEq"
    JGt -> "JGt"
    JGtEq -> "JGtEq"

-- Takes a test and runs it in ll code, printing the result and if it failed
runTestInLL :: (SExpr, JValue) -> IO ()
runTestInLL (se, ans) = do
    -- Convert to source code
    let je = desugar se
    let jeLL = jeToLL je
    let ansLL = jvToLL ans

    -- Print message
    putStrLn "========================="
    putStrLn $ "test=" ++ show se
    putStrLn $ "expecting=" ++ show ans

    -- Write the source to the hlgen file
    writeFile "../low-level/src/hlgen.rs" $
        unlines [ "use ll::*;"
                , "fn main() {"
                , "let expr =" ++ jeLL ++ ";"
                , "let ans =" ++ ansLL ++ ";"
                , "let val = Ck::evaluate(expr);"
                , "println!(\"answer={:?}\", val);"
                , "if val != ans { println!(\"!!! Failure !!!\"); }"
                , "}"
                ]

    -- Run the test program
    callCommand "cargo run --quiet --manifest-path=../low-level/Cargo.toml"

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
