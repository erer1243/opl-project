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

interp :: JExpr -> Integer
interp (JNum n) = n
interp (JPlus lhs rhs) = interp lhs + interp rhs
interp (JMult lhs rhs) = interp lhs * interp rhs

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

checkJExpr :: JExpr -> JValue -> Bool
checkJExpr expr ans = interp expr == ans

checkSExpr :: SExpr -> JValue -> Bool
checkSExpr expr = checkJExpr (desugar expr)

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
