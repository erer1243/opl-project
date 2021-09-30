-- For SExpr overloading
{-# LANGUAGE OverloadedStrings, OverloadedLists, TypeFamilies #-}

-- For SExpr overloading
import GHC.Exts (IsList(..))
import Data.String (IsString(..))

import Data.List (intercalate)
import System.Process (spawnCommand, waitForProcess)
import Control.Monad (forM_)
import Data.Char (isUpper)

-- prog ::= d... e
data JProg = JProg [JDefine] JExpr deriving (Show, Eq)

-- d ::= define (f x...) e
data JDefine = JDefine JFnRef [JVarRef] JExpr deriving (Show, Eq)

-- e ::= v | (e e..) | (if e e e) | x
data JExpr = JVal JValue
           | JApply JExpr [JExpr]
           | JIf JExpr JExpr JExpr
           | JVarRef JVarRef
           deriving (Show, Eq)

-- v ::= number | boolean | prim | f
-- prim ::= + | * | / | - | <= | < | = | > | >=
-- prim is not a separate data structure in my implementation
data JValue = JNum Integer
            | JBool Bool
            | JPlus | JMinus | JMult | JDiv | JLtEq | JLt | JEq | JGt | JGtEq
            | JFnRef JFnRef
            deriving (Show, Eq)

-- E ::= [] | (if E e e) | (v.. E e..)
data Context = CHole
             | CIf Context JExpr JExpr
             | CApp [JValue] Context [JExpr]
             deriving (Show, Eq)

-- f ::= some set of functions
type JFnRef = String

-- x ::= some set of variables
type JVarRef = String

-- se ::= empty | (cons se se) | string
-- I decided to implement SExpr this way because it allows me
-- to take advantage of list, string, and number literal overloading in ghc
-- to write SExprs like ["+", 1, 2]
data SExpr = SESym String | SENum Integer | SEList [SExpr] deriving (Show, Eq)

-- List of function definitions
type Delta = [(JFnRef, JDefine)]

pp = ppJP

ppJP :: JProg -> String
ppJP (JProg defns body) = unlines $ map ppJD defns ++ [ppJE body]

ppJD :: JDefine -> String
ppJD (JDefine f xs ebody) = "(define (" ++ commaSep (f : xs) ++ ") " ++ ppJE ebody ++ ")"

ppJE :: JExpr -> String
ppJE (JVal val) = case val of
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
    JFnRef s -> s
ppJE (JIf cond e1 e2) = "(if " ++ ppJE cond ++ " " ++ ppJE e1 ++ " " ++ ppJE e2 ++ ")"
ppJE (JApply head args) = "(" ++ ppJE head ++ " " ++ printedArgs ++ ")"
  where
    printedArgs = unwords $ map ppJE args
ppJE (JVarRef s) = s

-- Convenience alias
interp = interpJProg

-- Top level interp
interpJProg :: JProg -> JValue
interpJProg (JProg defns main) = interpJExpr delta main
  where
    delta = map toPair defns
    toPair def@(JDefine name _ _) = (name, def)

-- Interp a single JExpr
interpJExpr :: Delta -> JExpr -> JValue
interpJExpr delta expr = case expr of
    JVal v -> v
    JIf ec et ef -> if interpJExpr' ec == JBool False
                    then interpJExpr' ef
                    else interpJExpr' et
    JApply efn eargs -> let vfn = interpJExpr' efn
                            vargs = map interpJExpr' eargs
                        in runDelta delta vfn vargs
    JVarRef x -> error $ "Undefined variable " ++ x
  where
    interpJExpr' = interpJExpr delta

-- Delta function, renamed since we now have the delta argument
runDelta :: Delta -> JValue -> [JValue] -> JValue
runDelta _ JPlus [JNum a, JNum b] = JNum (a + b)
runDelta _ JMinus [JNum a, JNum b] = JNum (a - b)
runDelta _ JMult [JNum a, JNum b] = JNum (a * b)
runDelta _ JDiv [JNum a, JNum b] = JNum (a `div` b)
runDelta _ JLtEq [JNum a, JNum b] = JBool (a <= b)
runDelta _ JLt [JNum a, JNum b] = JBool (a < b)
runDelta _ JEq [JNum a, JNum b] = JBool (a == b)
runDelta _ JGt [JNum a, JNum b] = JBool (a > b)
runDelta _ JGtEq [JNum a, JNum b] = JBool (a >= b)
runDelta delta (JFnRef f) paramVals =
    let ebody' = maybe (error f) (substArrow paramVals) (lookup f delta)
    in interpJExpr delta ebody'
runDelta _ p vs = error $ "Bad JApply " ++ show p ++ " " ++ show vs

-- Substitute multiple parameters into a JDefine body
substArrow :: [JValue] -> JDefine -> JExpr
substArrow vs (JDefine f xs ebody)
    | length xs /= length vs = error $ f ++ ": bad param count"
    | otherwise = foldr subst ebody (zip xs vs)

-- Substitute a single variable into a JExpr
subst :: (JVarRef, JValue) -> JExpr -> JExpr
subst var@(x, xv) e = case e of
    e@(JVal _) -> e
    JIf ec et ef -> JIf (subst' ec) (subst' et) (subst' ef)
    JApply e0 em -> JApply (subst' e0) (map subst' em)
    JVarRef y | y == x -> JVal xv
              | otherwise -> JVarRef y
  where
    subst' = subst var

-- plug :: Context -> JExpr -> JExpr
-- plug CHole e = e
-- plug (CIf ctx et ef) e = JIf (plug ctx e) et ef
-- plug (CApp before ctx after) e = case before of
--     -- The context is the prim
--     [] -> JApply (plug ctx e) after
--     -- The context is an argument to the prim
--     before ->
--         let (prim:argsBefore) = map JVal before
--             args = argsBefore ++ plug ctx e : after
--         in JApply prim args

-- fr :: JExpr -> Maybe (Context, JExpr)
-- fr (JVal _ ) = Nothing
-- fr e@(JIf ec et ef) = case fr ec of
--     Nothing -> Just (CHole, e)
--     Just (ctx, rdx) -> Just (CIf ctx et ef, rdx)
-- fr e@(JApply prim args) =
--     case span isJVal applyList of
--         (v, []) -> Just (CHole, e)
--         (v, e0:em) ->
--             -- The above branch guarantees all elements in v are JVal
--             let vals = map unwrapJVal v
--                 Just (ctx, rdx) = fr e0
--             in Just (CApp vals ctx em, rdx)
--   where
--     applyList = prim : args
--     isJVal (JVal _) = True
--     isJVal _ = False

-- smallStepInterp :: JExpr -> JValue
-- smallStepInterp e = case fr e of
--     -- fr says that e is a JVal, so it is safe to unwrap it
--     Nothing -> unwrapJVal e
--     Just (ctx, rdx) -> smallStepInterp $ plug ctx $ step rdx

-- -- Usage of fr in smallStepInterp guarantees all parts
-- -- of each JExpr passed to step are a JVal
-- step :: JExpr -> JExpr
-- step (JIf (JVal (JBool False)) _ ef) = ef
-- step (JIf (JVal _) et _) = et
-- step (JApply p v) = JVal $ delta (unwrapJVal p) (map unwrapJVal v)
-- step _ = error "Bad step"

-- Convenience alias
desugar = desugarJProg

-- The top level desugarer
desugarJProg :: SExpr -> JProg
desugarJProg (SEList (SESym "prog":body)) =
    let defns = map desugarJDefine $ init body
        main = desugarJExpr $ last body
    in JProg defns main
desugarJProg _ = undefined

desugarJDefine :: SExpr -> JDefine
desugarJDefine (SEList [SESym "define", SEList (SESym name:params), body]) =
    JDefine name (map unwrapSESym params) (desugarJExpr body)
  where
    unwrapSESym (SESym s) = s
    unwrapSESym _ = undefined
desugarJDefine _ = undefined

desugarJExpr :: SExpr -> JExpr
desugarJExpr (SENum n) = JVal $ JNum n
desugarJExpr (SEList l) = case l of
    -- +/* base cases
    [SESym "+"] -> JVal $ JNum 0
    [SESym "*"] -> JVal $ JNum 1
    -- +/* recursive cases
    (plus@(SESym "+"):head:tail) -> JApply (JVal JPlus) [desugarJExpr head,
                                                         desugarJExpr $ SEList $ plus : tail]
    (mult@(SESym "*"):head:tail) -> JApply (JVal JMult) [desugarJExpr head,
                                                         desugarJExpr $ SEList $ mult : tail]
    -- negation
    [SESym "-", e] -> JApply (JVal JMult) [JVal (JNum (-1)), desugarJExpr e]
    -- conditional
    [SESym "if", ec, et, ef] -> JIf (desugarJExpr ec) (desugarJExpr et) (desugarJExpr ef)
    -- other apply
    (sym@(SESym _):tail) -> JApply (desugarJExpr sym) (map desugarJExpr tail)

    -- Error case
    l -> error $ "bad SEList " ++ show l
desugarJExpr (SESym s) = case s of
    -- Builtins
    "+" -> JVal JPlus
    "-" -> JVal JMinus
    "*" -> JVal JMult
    "/" -> JVal JDiv
    "=" -> JVal JEq
    "<" -> JVal JLt
    ">" -> JVal JGt
    "<=" -> JVal JLtEq
    ">=" -> JVal JGtEq
    "true" -> JVal $ JBool True
    "false" -> JVal $ JBool False
    -- Function or variable, depending on uppercase/lowercase
    s@(c:_) | isUpper c -> JVal $ JFnRef s
            | otherwise -> JVarRef s
    -- Empty string error case
    _ -> undefined

-- Helper function that unwraps a JValue from a JExpr JVal variant
-- In a couple places, we are guaranteed that a JExpr is a JVal
-- and this is useful. I believe I wrote the code in such a way that the
-- error branch is impossible to hit, even given a malformed JExpr.
unwrapJVal :: JExpr -> JValue
unwrapJVal (JVal v) = v
unwrapJVal e = error $ "unwrapJVal " ++ show e

checkJExprBig :: JProg -> JValue -> Bool
checkJExprBig prog ans = interp prog == ans

-- checkJExprSmall :: JExpr -> JValue -> Bool
-- checkJExprSmall expr ans = smallStepInterp expr == ans

checkSExpr :: SExpr -> JValue -> Bool
checkSExpr expr = checkJExprBig (desugarJProg expr)

-- [(program, expected_answer)]
tests :: [(SExpr, JValue)]
tests = [ (["prog", "<="], JLtEq)
        , (["prog", ["+", ["*", 2, 2], 1]], JNum 5)
        , (["prog", ["-", ["*", 5, ["+", 2, 3]]]], JNum (-25))
        , (["prog", ["define", ["One"], 1], "One"], JFnRef "One")
        , (["prog", ["define", ["One"], 1], ["One"]], JNum 1)
        , (["prog", ["define", ["CallSingle", "f"], ["f"]],
                    ["define", ["One"], 1],
                    ["CallSingle", "One"]], JNum 1)
        , (["prog", ["define", ["Double", "x"], ["+", "x", "x"]], ["Double", ["Double", 2]]], JNum 8)
        , (["prog", ["define", ["Quintuple", "x"], ["+", "x", "x", "x", "x", "x"]],
                               ["Quintuple", ["Quintuple", 1]]], JNum 25)
        , (["prog", ["define", ["Quadruple", "x"], ["Double", ["Double", "x"]]],
                    ["define", ["Double", "x"], ["*", "x", 2]],
                    ["Quadruple", 4]], JNum 16)
        , (["prog", ["define", ["Recurse", "x"], ["if", ["=", "x", 0],
                                                        123,
                                                        ["Recurse", ["-", "x", 1]]]],
                    ["Recurse", 10000]], JNum 123)
        , (["prog", ["define", ["Recurse1", "x"], ["Recurse2", ["+", "x", 1]]],
                    ["define", ["Recurse2", "x"], ["if", [">", "x", 10000], "x", ["Recurse1", "x"]]],
                    ["Recurse1", 0]], JNum 10001)
        , (["prog", ["define", ["Recurse1", "x"], ["Recurse2", ["+", "x", 2]]],
                    ["define", ["Recurse2", "x"], ["Recurse3", ["-", "x", 1]]],
                    ["define", ["Recurse3", "x"], ["if", [">", "x", 10000], "x", ["Recurse1", "x"]]],
                    ["Recurse1", 0]], JNum 10001)
        -- Evals to the highest number found during the collatz process for 27
        , (["prog", ["define", ["CollatzHighest", "x", "h"], ["if", ["IsEven", "x"],
                                                                    ["Eq1", ["/", "x", 2], "h"],
                                                                    ["Eq1", ["+", 1, ["*", "x", 3]], "h"]]],
                    ["define", ["Eq1", "x", "h"], ["if", ["=", "x", 1],
                                                         "h",
                                                         ["NewHighest", "x", "h"]]],
                    ["define", ["NewHighest", "x", "h"], ["if", [">", "x", "h"],
                                                                ["CollatzHighest", "x", "x"],
                                                                ["CollatzHighest", "x", "h"]]],
                    ["define", ["IsEven", "x"], ["=", "x", ["*", 2, ["/", "x", 2]]]],
                    ["CollatzHighest", 27, 0]], JNum 9232)
        -- Dynamic scope tests
        , (["prog", ["define", ["F", "x"], "y"],
                    ["define", ["G", "y"], ["F", 0]],
                    ["G", 1]], JFnRef "Test should fail")
        , (["prog", ["define", ["F", "x"], "true"],
                    ["if", ["F", 0], "x", "x"]], JFnRef "Test should fail")
        ]

runTests :: IO ()
runTests = do
    -- putStrLn "Running tests in HL code:"
    -- let testResults = map (uncurry checkSExpr) tests
    -- let numSuccesses = length $ filter id testResults
    -- let numFailures = length tests - numSuccesses
    -- putStrLn $ show numSuccesses ++ " successes and " ++ show numFailures ++ " failures"

    putStrLn "Running tests in LL code:"
    forM_ tests runTestInLL

-- Convert JProg to rust code
jpToLL :: JProg -> String
jpToLL (JProg defns main) = "JProg(" ++ listToLL (map jdToLL defns) ++ "," ++ jeToLL main ++ ")"

-- Convert JDefine to rust code
jdToLL :: JDefine -> String
jdToLL (JDefine name args body) = "JDefine(" ++ strToLL name ++ ","
                                             ++ listToLL (map strToLL args) ++ ","
                                             ++ jeToLL body ++ ")"

-- Converts a single JExpr to low level rust code.
jeToLL :: JExpr -> String
jeToLL (JVal v) = "jval(" ++ jvToLL v ++ ")"
jeToLL (JIf ec et ef) = "jif(" ++ commaSep (map jeToLL [ec, et, ef]) ++ ")"
jeToLL (JApply p args) = "japply(" ++ jeToLL p ++ "," ++ listToLL (map jeToLL args) ++ ")"
jeToLL (JVarRef s) = "jvarref(" ++ strToLL s ++ ")"

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
    JFnRef s -> "JFnRef(" ++ strToLL s ++ ")"

commaSep :: [String] -> String
commaSep  = intercalate ", "

listToLL :: [String] -> String
listToLL strs = "List::from([" ++ commaSep strs ++ "])"

strToLL :: String -> String
strToLL s = "\"" ++ s ++ "\""

-- Takes a test and runs it in ll code, printing the result and if it failed
runTestInLL :: (SExpr, JValue) -> IO ()
runTestInLL (se, ans) = do
    -- Convert to source code
    let je = desugarJProg se
    let jeLL = jpToLL je
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
                , "let val = Cek::evaluate(expr);"
                , "println!(\"answer={:?}\", val);"
                , "if val != ans { println!(\"!!! Failure !!!\"); }"
                , "}"
                ]

    -- Run the test program
    runCommand "cargo run --quiet --manifest-path=../low-level/Cargo.toml"

-- Run a command and ignore exit code. We expect some tests to fail and exit failure
runCommand :: String -> IO ()
runCommand s = spawnCommand s >>= waitForProcess >> return ()

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
