-- For SExpr overloading
{-# LANGUAGE OverloadedStrings, OverloadedLists, TypeFamilies #-}

-- For SExpr overloading
import GHC.Exts (IsList(..))
import Data.String (IsString(..))

import Data.List (intercalate)
import System.Process (spawnCommand, waitForProcess)
import Control.Monad (forM_)

-- Types from page 9-2
-- (obj [x: e]), (obj [x: v]), (ref e x) are implemented using desugaring and
-- standard library functions that exist from the first half of lecture 9
-- The only exceptions is that JField and JStrEq are implemented in the actual
-- language.
data JExpr = JVal JValue
           | JApply JExpr [JExpr]
           | JIf JExpr JExpr JExpr
           | JVarRef JVarRef
           | JCase JExpr (JVarRef, JExpr) (JVarRef, JExpr)
           deriving (Show, Eq)

data JValue = JNum Integer
            | JBool Bool
            | JLambda JVarRef [JVarRef] JExpr
            | JPlus | JMinus | JMult | JDiv | JLtEq | JLt | JEq | JGt | JGtEq
            | JUnit | JPair JValue JValue | JInl JValue | JInr JValue
            | JInlOp | JInrOp | JPairOp | JFst | JSnd
            | JField JVarRef | JStrEq
            deriving (Show, Eq)

type JVarRef = String

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
    JInlOp -> "inl"
    JInrOp -> "inr"
    JPairOp -> "pair"
    JFst -> "fst"
    JSnd -> "snd"
    JUnit -> "unit"
    JInl v -> "(inl " ++ pp (JVal v) ++ ")"
    JInr v -> "(inr " ++ pp (JVal v) ++ ")"
    JPair vl vr -> "(pair " ++ pp (JVal vl) ++ " " ++ pp (JVal vr) ++ ")"
    JField s -> s
    JStrEq -> "string=?"
    JLambda f xs ebody -> "(λ " ++ f ++ " (" ++ unwords (map (pp . JVarRef) xs) ++ ") " ++ pp ebody
                            ++ ")"
pp (JIf cond e1 e2) = "(if " ++ pp cond ++ " " ++ pp e1 ++ " " ++ pp e2 ++ ")"
pp (JApply e0 en) = let ppEn = if null en then "" else " " ++ unwords (map pp en)
                    in "(" ++ pp e0 ++ ppEn ++ ")"
pp (JVarRef s) = s
pp (JCase e (xl, el) (xr, er)) = "(case " ++ pp e ++ " (inl " ++ xl ++ " => " ++ pp el ++ ")"
                                                  ++ " (inr " ++ xr ++ " => " ++ pp er ++ "))"

desugar :: SExpr -> JExpr
desugar (SENum n) = JVal $ JNum n
desugar (SEList l) = case l of
    -- +/* base cases
    [SESym "+"] -> JVal $ JNum 0
    [SESym "*"] -> JVal $ JNum 1
    -- +/* recursive cases
    (plus@(SESym "+"):n:rest) -> JApply (JVal JPlus) [desugar n,
                                                      desugar $ SEList $ plus : rest]
    (mult@(SESym "*"):n:rest) -> JApply (JVal JMult) [desugar n,
                                                      desugar $ SEList $ mult : rest]
    -- negation
    [SESym "-", e] -> JApply (JVal JMult) [JVal (JNum (-1)), desugar e]
    -- conditional
    [SESym "if", ec, et, ef] -> JIf (desugar ec) (desugar et) (desugar ef)
    -- lambda
    [SESym "lambda", SEList xs, ebody] -> JVal $ JLambda "rec" (map unwrapSESym xs) (desugar ebody)
    [SESym "lambda", SESym f, SEList xs, ebody] -> JVal $ JLambda f (map unwrapSESym xs)
                                                                    (desugar ebody)
    -- let form
    [SESym "let", SEList binds, ebody] -> let (xs, es) = desugarLetPairs binds
                                          in JApply (JVal $ JLambda "rec" xs (desugar ebody)) es
    -- let* form base case
    [SESym "let*", SEList [], ebody] -> desugar ebody
    -- let* form recursive case
    [SESym "let*", SEList (x:e:binds), ebody] ->
        desugar ["let", [x, e], ["let*", SEList binds, ebody]]
    -- do-times macro
    [SESym "do-times", x@(SESym _), ec, ans@(SESym _), ed, eb] ->
        desugar ["let", ["last", ec], [[λ, [x, ans], ["if", ["<", x, "last"],
                                                         ["rec", ["+", x, 1], eb], ans]],
                                        0, ed]]
    -- case
    [SESym "case", e, SEList [SESym xl, el], SEList [SESym xr, er]] ->
        JCase (desugar e) (xl, desugar el) (xr, desugar er)
    -- obj creation base case
    [SESym "obj", SEList []] -> desugar "obj-empty"
    -- obj creation recursive case
    [SESym "obj", SEList ((SESym x):e:binds)] ->
        let tailObj = desugar ["obj", SEList binds]
        in JApply (desugar "obj-set") [tailObj, JVal (JField x), desugar e]
    -- obj field access / dot syntax
    [SESym "ref", e, SESym x] -> JApply (desugar "obj-lookup") [desugar e, JVal (JField x)]
    -- general apply
    (sym:args) -> JApply (desugar sym) (map desugar args)
    -- Error case
    _ -> error $ "bad SEList " ++ show l
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
    "inl" -> JVal JInlOp
    "inr" -> JVal JInrOp
    "pair" -> JVal JPairOp
    "unit" -> JVal JUnit
    "fst" -> JVal JFst
    "snd" -> JVal JSnd
    "string=?" -> JVal JStrEq
    -- Anything else -> var ref
    _ -> JVarRef s

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
tests = [
          -- Basic functionality tests
          (1, JNum 1)
        , ("<=", JLtEq)
        , ([["lambda", [], 1]], JNum 1)
        , (["let", [], ["-", 25]], JNum (-25))
        , (["let", ["x", 1], "x"], JNum 1)
        , (["let", ["x", 1, "y", 2, "z", 3], ["+", "x", "y", "z"]], JNum 6)
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
        -- Shadowing variables test
        , (["let", ["x", 5], ["let", ["x", 10], "x"]], JNum 10)
        , (["let*", ["x", 5, "x", 10], "x"], JNum 10)
        , (["let", ["x", 10, "f", ["lambda", ["x"], "x"]], ["+", "x", ["f", 5]]], JNum 15)

        -- Testing of closing over variables !!!!TODO!!!!!
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

        -- J4 tests
        , ([[λ, ["n"], ["if", ["=", "n", 0], 1, ["*", "n", ["rec", ["-", "n", 1]]]]], 6], JNum 720) -- 6!
        , (["let", ["useless-recurse", [λ, ["n"], ["if", ["=", "n", 0], 123, ["rec", ["-", "n", 1]]]]],
              ["useless-recurse", 100000]], JNum 123) -- Recurse 100000 times to show it works
        , (["let", ["sumN", [λ, ["n"], ["if", ["=", "n", 0], 0, ["+", "n", ["rec", ["-", "n", 1]]]]]],
              ["sumN", 5]], JNum 15) -- 0+1+2+3+4+5
        , (["let", ["fac", [λ, "fac", ["n"], ["if", ["=", "n", 0], 1, ["*", "n", ["fac", ["-", "n", 1]]]]]],
              ["fac", 5]], JNum 120) -- 5! using basic recursion
        , (["nat-unfold", "+", 0, 5], JNum 15) -- 5+4+3+2+1+0
        , (["nat-unfold", "-", 0, 5], JNum 3) -- 5-(4-(3-(2-(1-0))))
        , (["nat-unfold", "*", 1, 5], JNum 120) -- 5! using nat-unfold
        , (["nat-unfold", [λ, ["_", "n"], ["+", "n", 1]], 0, 5], JNum 5) -- 1+1+1+1+1+0
        , (["do-times", "i", 5, "sum", 0, ["+", "i", "sum"]], JNum 10) -- 0+1+2+3+4
        , (["let", ["fac", [λ, ["n"], ["nat-unfold", "*", 1, "n"]]],
               ["do-times", "i", 5, "sum", 0, ["+", ["fac", "i"], "sum"]]], JNum 34) -- 0!+1!+2!+3!+4!
        , (["let", ["fac", [λ, ["n"],
                       ["do-times", "i", ["+", "n", 1], "sum", 1,
                           ["*", "sum", ["if", ["=", "i", 0], 1, "i"]]]]],
               ["fac", 5]], JNum 120) -- 5! using do-times
        , (["let*", ["pow2", [λ, ["n"], ["do-times", "i", "n", "m", 1, ["*", 2, "m"]]],
                     "fill-bits", [λ, ["n"], ["do-times", "i", "n", "sum", 0,
                                                 ["+", "sum", ["pow2", "i"]]]],
                     "and", [λ, ["b1", "b2"], ["if", "b1", "b2", "false"]]],
            ["and", ["=", ["fill-bits", 6], 63], -- fill-bits 6 = 0b111111 = 63
                ["and", ["=", ["fill-bits", 7], 127], -- 0b1111111 = 127
                        ["=", ["fill-bits", 8], 255]]]], JBool True) -- 0b11111111 = 256

        -- J5 raw extension tests
        , ("unit", JUnit)
        , (["inr", 5], JInr (JNum 5))
        , (["pair", ["inl", ["pair", ">", "<"]], "false"], JPair (JInl (JPair JGt JLt)) (JBool False))
        , (["case", ["inl", "unit"], ["_", "<"], ["_", ">"]], JLt)
        , (["case", ["inl", 5], ["l", ["+", "l", 10]], ["r", "false"]], JNum 15)
        , (["fst", ["pair", 5, "true"]], JNum 5)
        , (["snd", ["pair", 5, "true"]], JBool True)
        , (["let", ["numToUnary", [λ, ["n"], ["if", ["=", "n", 0],
                                                    ["inl", "unit"],
                                                    ["inr", ["rec", ["-", "n", 1]]]]],
                    "unaryToNum", [λ, ["u"], ["case", "u", ["l", 0], ["r", ["+", 1, ["rec", "r"]]]]]],

                   ["unaryToNum", ["numToUnary", 100]]], JNum 100)
        , (["ref", ["obj", ["a", 5, "b", 10]], "b"], JNum 10)
        , (["let", ["o", ["obj", ["a", ["*", 1, 2, 3],
                                  "b", ["pair", "false", 10]]]],
                   ["+", ["ref", "o", "a"], ["snd", ["ref", "o", "b"]]]], JNum 16)
        , (["let*", ["a", ["obj", ["sub", "-"]],
                     "b", ["obj", ["nested-a", "a"]],
                     "c", ["obj", ["nested-b", "b", "x", 10, "y", 4]],
                     "op", ["ref", ["ref", ["ref", "c", "nested-b"], "nested-a"], "sub"]],
                    ["op", ["ref", "c", "x"], ["ref", "c", "y"]]], JNum 6)

        -- J5 standard library tests
        , ("empty", JInl JUnit)
        , (["length", "empty"], JNum 0)
        , (["length", listToSe [1..10]], JNum 10)
        , (["map", [λ, ["n"], ["+", "n", 3]], listToSe [1..5]], listToJv [4..8])
        , (["reduce", "*", 1, listToSe [2..5]], JNum (2 * 3 * 4 * 5))
        , (["filter", [λ, ["n"], ["<", "n", 5]], listToSe ([1..10] ++ [10,9..1])],
           listToJv ([1..4] ++ [4,3..1]))
        , (["reduce", "+", 0,
               ["filter", [λ, ["n"], ["<", "n", 40]],
                   ["map", [λ, ["n"], ["*", "n", "n"]], listToSe [1..10]]]],
           JNum (sum $ filter (< 40) $ map (^ 2) [1..10]) )
        , (["append", "empty", "empty"], listToJv [])
        , (["append", listToSe [1..3], listToSe [4..6]], listToJv [1..6])
        , (["let", ["list-empty?", [λ, ["l"], ["case", "l", ["_", "true"], ["_", "false"]]]],
               ["and", ["list-empty?", "empty"],
                       ["not", ["list-empty?", listToSe [1]]]]], JBool True)
        , (["let", ["zip", [λ, ["x", "y"], ["case", "x",
                                               ["_", "empty"],
                                               ["px", ["case", "y",
                                                   ["_", "empty"],
                                                   ["py", ["cons", ["pair", ["fst", "px"], ["fst", "py"]],
                                                                   ["rec", ["snd", "px"], ["snd", "py"]]]]]]]]],
                   ["zip", listToSe [1, 2], listToSe [4..10]]],
           JInr (JPair (JPair (JNum 1) (JNum 4)) (JInr (JPair (JPair (JNum 2) (JNum 5)) (JInl JUnit)))))
        , (["let*", ["head", [λ, ["l"], ["case", "l", ["_", "nothing"], ["p", ["just", ["fst", "p"]]]]],
                     "tail", [λ, ["l"], ["case", "l", ["_", "nothing"], ["p", ["just", ["snd", "p"]]]]],
                     "is-just?", [λ, ["o"], ["case", "o", ["_", "false"], ["_", "true"]]],
                     "is-none?", [λ, ["o"], ["not", ["is-just?", "o"]]],
                     "unwrap-just", [λ, ["j"], ["case", "j", ["_", "error"], ["e", "e"]]],

                     "l", listToSe [5..10],
                     "a", ["=", ["unwrap-just", ["head", "l"]], 5],
                     "b", ["is-just?", ["tail", "l"]],
                     "c", ["is-none?", ["head", "empty"]],
                     "d", ["is-none?", ["tail", "empty"]]],

                    ["reduce", "or", "true",
                        ["cons", "a", ["cons", "b", ["cons", "c", ["cons", "d", "empty"]]]]]], JBool True)
        ]

-- Convenience functions for j5 stdlib testing
-- Converts a number list to the JValue representation
listToJv :: [Integer] -> JValue
listToJv = foldr (\n v -> JInr (JPair (JNum n) v)) (JInl JUnit)

-- Converts a number list to the SExpr representation
listToSe :: [Integer] -> SExpr
listToSe = foldr (\n e -> ["cons", SENum n, e]) "empty"

-- Convenience alias to make lambda code shorter
λ :: SExpr
λ = "lambda"

-- Add standard library functions to some code
addStdlibToSE :: SExpr -> SExpr
addStdlibToSE se = ["let*", stdlib, se]
  where
    stdlib = [ "nat-unfold", [λ, "nat-unfold", ["f", "z", "n"],
                                 ["if", ["=", "n", 0],
                                     "z", ["f", "n", ["nat-unfold", "f", "z", ["-", "n", 1]]]]]
             -- Standard library functions from lecture 9
             , "empty", ["inl", "unit"]
             , "cons", [λ, ["data", "rest"], ["inr", ["pair", "data", "rest"]]]
             , "length", [λ, ["list"], ["case", "list", ["_", 0],
                                                        ["p", ["+", 1, ["rec", ["snd", "p"]]]]]]
             , "obj-empty", "empty"
             , "obj-set", [λ, ["o", "x", "e"], ["cons", ["pair", "x", "e"], "o"]]
             , "obj-lookup", [λ, ["o", "k"], ["case", "o", ["_", "obj-lookup failed"],
                                                           ["r", ["if", ["string=?", "k", ["fst", ["fst", "r"]]],
                                                                        ["snd", ["fst", "r"]],
                                                                        ["rec", ["snd", "r"], "k"]]]]]
             , "map", [λ, ["f", "l"], ["case", "l", ["_", "l"],
                                                    ["p", ["cons", ["f", ["fst", "p"]],
                                                                   ["rec", "f", ["snd", "p"]]]]]]
             , "reduce", [λ, ["f", "z", "l"],
                             ["case", "l", ["_", "z"],
                                           ["p", ["rec", "f", ["f", "z", ["fst", "p"]], ["snd", "p"]]]]]
             , "filter", [λ, ["pr", "l"],
                             ["case", "l", ["_", "l"],
                                           ["p", ["let", ["r'", ["rec", "pr", ["snd", "p"]]],
                                                         ["if", ["pr", ["fst", "p"]],
                                                                ["cons", ["fst", "p"], "r'"],
                                                                "r'"]]]]]
             , "append", [λ, ["x", "y"], ["case", "x", ["_", "y"],
                                                       ["p", ["cons", ["fst", "p"],
                                                                      ["rec", ["snd", "p"], "y"]]]]]
             , "nothing", "empty"
             , "just", "inr"
             -- Other standard library functions I added
             , "or", [λ, ["a", "b"], ["if", "a", "true", "b"]]
             , "and", [λ, ["a", "b"], ["if", "a", "b", "false"]]
             , "not", [λ, ["b"], ["if", "b", "false", "true"]]
             ]

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
              "pair_", [λ, ["l"], [λ, ["r"], [λ, ["s"],
                        [["s", "l"], "r"] ]]],
              "fst_", [λ, ["p"], ["p", "true_"]],
              "snd_", [λ, ["p"], ["p", "false_"]],
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
                        ["fst_", [["n", [λ, ["p"], [["pair_", ["snd_", "p"]], ["add1", ["snd_", "p"]]]]],
                                       [["pair_", "zero"], "zero"]]]],
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

-- Converts a single JExpr to low level rust code.
jeToLL :: JExpr -> String
jeToLL (JVal v) = "jval(" ++ jvToLL v ++ ")"
jeToLL (JIf ec et ef) = "jif(" ++ commaSep (map jeToLL [ec, et, ef]) ++ ")"
jeToLL (JApply p args) = "japply(" ++ jeToLL p ++ "," ++ listToLL (map jeToLL args) ++ ")"
jeToLL (JVarRef s) = "jvarref(" ++ strToLL s ++ ")"
jeToLL (JCase e (xl, el) (xr, er)) = "jcase(" ++ jeToLL e
                                              ++ ", (" ++ commaSep [strToLL xl, jeToLL el] ++ ")"
                                              ++ ", (" ++ commaSep [strToLL xr, jeToLL er] ++ "))"

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
    JLambda f xs ebody ->
        "JLambda(" ++ commaSep [strToLL f, listToLL (map strToLL xs), jeToLL ebody] ++ ")"
    JUnit -> "JUnit"
    JInrOp -> "JInrOp"
    JInlOp -> "JInlOp"
    JPairOp -> "JPairOp"
    JFst -> "JFst"
    JSnd -> "JSnd"
    JInl v -> "JInl(" ++ leakWrap (jvToLL v) ++ ")"
    JInr v -> "JInr(" ++ leakWrap (jvToLL v) ++ ")"
    JPair l r -> "JPair(" ++ commaSep (map (leakWrap . jvToLL) [l, r]) ++ ")"
    JField s -> "JField(" ++ strToLL s ++ ")"
    JStrEq -> "JStrEq"

commaSep :: [String] -> String
commaSep  = intercalate ", "

listToLL :: [String] -> String
listToLL strs = "List::from([" ++ commaSep strs ++ "])"

strToLL :: String -> String
strToLL s = "\"" ++ s ++ "\""

leakWrap :: String -> String
leakWrap s = "Leak::new(" ++ s ++ ")"

-- Takes a test and runs it in ll code, printing the result and if it failed
runTestInLL :: (SExpr, JValue) -> IO ()
runTestInLL (se, ans) = do
    -- Convert to source code
    let je = desugar $ addStdlibToSE se
    let jeLL = jeToLL je
    let ansLL = jvToLL ans

    -- Print message
    putStrLn "========================="
    putStrLn $ "expr=" ++ pp (desugar se) -- Exclude standard library from test print
    putStrLn $ "expecting=" ++ show ans

    -- Write the source to the generated code file
    writeFile "../low-level/src/hlgen.rs" $
        unlines [ "#[allow(unused_imports)]"
                , "use ll::*;"
                , "fn main() {"
                , "let expr =" ++ jeLL ++ ";"
                , "let ans =" ++ ansLL ++ ";"
                , "let val = Cek::evaluate(expr);"
                , "println!(\"answer={:?}\", val);"
                , "if val == ans {"
                , "println!(\"{}\", ansi_term::Colour::Green.paint(\"Success\"));"
                , "} else {"
                , "panic!(\"{}\", ansi_term::Colour::Red.paint(\"!!! Test Failure !!!\"));"
                , "}"
                , "}"
                ]

    -- Run the test program
    runCommand "cargo run --quiet --manifest-path=../low-level/Cargo.toml"

-- Run a command and ignore exit code. This allows tests to continue if one fails
runCommand :: String -> IO ()
runCommand s = spawnCommand s >>= waitForProcess >> return ()

main :: IO ()
main = forM_ tests runTestInLL

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
