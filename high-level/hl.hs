-- For SExpr overloading
{-# LANGUAGE OverloadedStrings, OverloadedLists, TypeFamilies #-}

-- For SExpr overloading
import GHC.Exts (IsList(..))
import Data.String (IsString(..))

import Data.List (intercalate)
import System.Process (spawnCommand, waitForProcess)
import Control.Monad (forM_)

-- e ::= v | (e e...) | (if e e e) | x
data JExpr = JVal JValue
           | JApply JExpr [JExpr]
           | JIf JExpr JExpr JExpr
           | JVarRef JVarRef
           deriving (Show, Eq)

-- v ::= number | boolean | prim | lambda (x...) e
data JValue = JNum Integer
            | JBool Bool
            | JPlus | JMinus | JMult | JDiv | JLtEq | JLt | JEq | JGt | JGtEq
            | JLambda [JVarRef] JExpr
            deriving (Show, Eq)

-- E ::= [] | (if E e e) | (v.. E e..)
data Context = CHole
             | CIf Context JExpr JExpr
             | CApp [JValue] Context [JExpr]
             deriving (Show, Eq)

-- x ::= some set of variables
type JVarRef = String

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
    JLambda xs ebody -> "(λ (" ++ unwords (map (pp . JVarRef) xs) ++ ") " ++ pp ebody ++ ")"
pp (JIf cond e1 e2) = "(if " ++ pp cond ++ " " ++ pp e1 ++ " " ++ pp e2 ++ ")"
pp (JApply head args) = let ppArgs = if null args then "" else " " ++ unwords (map pp args)
                        in "(" ++ pp head ++ ppArgs ++ ")"
pp (JVarRef s) = s

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
    [SESym "-", e] -> JApply (JVal JMult) [JVal (JNum (-1)), desugar e]
    -- conditional
    [SESym "if", ec, et, ef] -> JIf (desugar ec) (desugar et) (desugar ef)
    -- lambda
    [SESym "lambda", SEList xs, ebody] -> JVal $ JLambda (map unwrapSESym xs) (desugar ebody)
    -- let form
    [SESym "let", SEList binds, ebody] -> let (xs, es) = desugarLetPairs binds
                                          in JApply (JVal $ JLambda xs (desugar ebody)) es
    -- let* form base case
    [SESym "let*", SEList [], ebody] -> desugar ebody
    -- let* form recursive case
    [SESym "let*", SEList (x:e:binds), ebody] -> desugar ["let", [x, e],
                                                                 ["let*", SEList binds, ebody]]
    -- apply
    (sym:tail) -> JApply (desugar sym) (map desugar tail)
    -- Error case
    l -> error $ "bad SEList " ++ show l
desugar (SESym s) = case s of
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
    s -> JVarRef s

-- Helper for desugaring let expressions
desugarLetPairs :: [SExpr] -> ([JVarRef], [JExpr])
desugarLetPairs binds = helper binds [] []
  where
    helper [] xs es = (map unwrapSESym xs, map desugar es)
    helper (x:v:t) xs es = helper t (x:xs) (v:es)
    helper _ _ _ = error $ "let has odd # of args to bindings: " ++ show binds

unwrapSESym :: SExpr -> String
unwrapSESym (SESym s) = s
unwrapSESym se = error $ "unwrapSESym on " ++ show se

-- [(program, expected_answer)]
tests :: [(SExpr, JValue)]
tests = [ (1, JNum 1)
        , ("<=", JLtEq)
        , ([["lambda", [], 1]], JNum 1)
        , (["let", [], ["-", 25]], JNum (-25))
        , (["let", ["x", 1], "x"], JNum 1)
        , (["let", ["x", 1, "y", 2], ["+", "x", "y"]], JNum 3)
        , (["let", ["x", -1, "y", 10, "z", 30], ["*", "x", "y", "z"]], JNum (-300))
        , (["let", ["add1", ["lambda", ["x"], ["+", "x", 1]]], ["add1", 20]], JNum 21)
        , (["let", ["app0", ["lambda", ["f"], ["f"]],
                    "one", ["lambda", [], 1]],
                   ["app0", "one"]], JNum 1)
        , (["let", ["app1", ["lambda", ["f", "x"], ["f", "x"]],
                    "add1", ["lambda", ["x"], ["+", "x", 1]]], ["app1", "add1", 5]], JNum 6)
        , (["let", ["prim", ["if", [">", 10, 11], ">", "<="]], ["prim", 3, 2]], JBool False)
        , (["let", ["x", 1], ["let", ["y", 2], ["let", ["p", "+", "z", 5],
                                                       ["p", "z", ["p", "y", ["-", "x"]]]]]], JNum 6)
        , (["let", ["curriedMult", ["lambda", ["x"], ["lambda", ["y"], ["*", "x", "y"]]]],
                   ["let",  ["mult5", ["curriedMult", 5],
                             "mult10", ["curriedMult", 10]],
                            ["+", ["mult5", 20], ["mult10", 5]]]], JNum 150)
        , (["let*", ["x", 5, "y", ["+", "x", 10], "z", ["*", "x", "y", 3]], "z"], JNum 225)
        , (["let*", ["curriedAdd", ["lambda", ["x"], ["lambda", ["y"], ["+", "x", "y"]]],
                     "add5", ["curriedAdd", 5],
                     "add10", ["curriedAdd", 10]],
                    ["add10", ["add5", ["add10", 100]]]], JNum 125)
        -- Task 35 lambda calculus/factorial tests
        , (task35Test ["numToJ3", ["factorial", "zero"]], JNum 1)
        , (task35Test ["numToJ3", ["factorial", "one"]], JNum 1)
        , (task35Test ["numToJ3", ["factorial", ["add1", "one"]]], JNum 2)
        , (task35Test ["numToJ3", ["factorial", ["add1", ["add1", "one"]]]], JNum 6)
        , (task35Test ["numToJ3", ["factorial", ["add1", ["add1", ["add1", "one"]]]]], JNum 24)
        , (task35Test ["numToJ3", ["factorial", ["add1", ["add1", ["add1", ["add1", "one"]]]]]], JNum 120)
        , (task35Test ["numToJ3", ["factorial", ["add1", ["add1", ["add1", ["add1", ["add1", "one"]]]]]]], JNum 720)
        ]

-- Convenience alias to make lambda code shorter
λ :: SExpr
λ = "lambda"

-- Takes an sexpr and puts it into the task 35
-- lambda calculus "standard library". For convenience of
-- testing multiple parts of my task 35 code.
task35Test :: SExpr -> SExpr
task35Test ebody =
    ["let*", [
              -- Booleans
              "true_", [λ, ["t"], [λ, ["f"], "t"]],
              "false_", [λ, ["t"], [λ, ["f"], "f"]],
              "if_", [λ, ["c"], "c"],
              -- Pairs
              "pair", [λ, ["l"], [λ, ["r"], [λ, ["s"],
                        [["s", "l"], "r"] ]]],
              "fst", [λ, ["p"], ["p", "true_"]],
              "snd", [λ, ["p"], ["p", "false_"]],
              -- Numbers and numeric operations
              "zero", [λ, ["f"], [λ, ["x"], "x"]],
              "one", [λ, ["f"], [λ, ["x"], ["f", "x"]]],
              "zero?", [λ, ["n"], [["n", [λ, ["x"], "false_"]], "true_"]],
              "add", [λ, ["n"], [λ, ["m"], [λ, ["f"], [λ, ["x"],
                       [["n", "f"], [["m", "f"], "x"]] ]]]],
              "mult", [λ, ["n"], [λ, ["m"], [λ, ["f"], [λ, ["x"],
                        [["n", ["m", "f"]], "x"] ]]]],
              "add1", [λ, ["n"], [["add", "n"], "one"] ],
              "sub1", [λ, ["n"],
                        ["fst", [["n", [λ, ["p"], [["pair", ["snd", "p"]], ["add1", ["snd", "p"]]]]],
                                       [["pair", "zero"], "zero"]]]],
              -- Z combinator
              "Z", [λ, ["f"], [[λ, ["x"], ["f", [λ, ["v"], [["x", "x"], "v"]]]],
                               [λ, ["x"], ["f", [λ, ["v"], [["x", "x"], "v"]]]]] ],
              -- Factorial
              "make-factorial", [λ, ["fac"], [λ, ["n"],
                                  [[[["if_", ["zero?", "n"]],
                                       [λ, ["x"], "one"] ],
                                       [λ, ["x"], [["mult", "n"], ["fac", ["sub1", "n"]]]] ],
                                   "zero"] ]],
              "factorial", ["Z", "make-factorial"],
              -- Convert a church encoded number to a J3 number
              "numToJ3", [λ, ["n"], [["n", [λ, ["m"], ["+", "m", 1]]], 0]]
             ],
             ebody
    ]

runTests :: IO ()
runTests = forM_ tests runTestInLL

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
    JLambda xs ebody -> "JLambda(" ++ commaSep [listToLL (map strToLL xs), jeToLL ebody] ++ ")"

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
    let je = desugar se
    let jeLL = jeToLL je
    let ansLL = jvToLL ans

    -- Print message
    putStrLn "========================="
    --putStrLn $ "test=" ++ show se
    putStrLn $ "expr=" ++ pp je
    putStrLn $ "expecting=" ++ show ans

    -- Write the source to the hlgen file
    writeFile "../low-level/src/hlgen.rs" $
        unlines [ "#[allow(unused_imports)]"
                , "use ll::*;"
                , "fn main() {"
                , "let expr =" ++ jeLL ++ ";"
                , "let ans =" ++ ansLL ++ ";"
                , "let val = Cek::evaluate(expr);"
                , "println!(\"answer={:?}\", val);"
                , "if val != ans { panic!(\"!!! Test Failure !!!\"); }"
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
