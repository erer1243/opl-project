-- For SExpr overloading
{-# LANGUAGE OverloadedStrings, OverloadedLists, TypeFamilies #-}

-- For SExpr overloading
import GHC.Exts (IsList(..))
import Data.String (IsString(..))

data JExpr = JNum Integer | JPlus JExpr JExpr | JMult JExpr JExpr deriving (Show)

data SExpr = SESym String | SENum Integer | SEList [SExpr] deriving (Show, Eq)

pp :: JExpr -> String
pp (JNum n) = show n
pp (JPlus lhs rhs) = "(+ " ++ pp lhs ++ " " ++ pp rhs ++ ")"
pp (JMult lhs rhs) = "(* " ++ pp lhs ++ " " ++ pp rhs ++ ")"

interp :: JExpr -> Integer
interp (JNum n) = n
interp (JPlus lhs rhs) = interp lhs + interp rhs
interp (JMult lhs rhs) = interp lhs * interp rhs

desugar :: SExpr -> JExpr
desugar (SEList l) = case l of
    -- +/* base cases
    [SESym "+"] -> JNum 0
    [SESym "*"] -> JNum 1
    -- +/* recursive cases
    (plus@(SESym "+"):sexpr:rest) -> JPlus (desugar sexpr) (desugar (SEList (plus : rest)))
    (mult@(SESym "*"):sexpr:rest) -> JMult (desugar sexpr) (desugar (SEList (mult : rest)))
    -- negation/subtraction
    [SESym "-", se] -> JMult (JNum (-1)) (desugar se)
    [SESym "-", e0, e1] -> JPlus (desugar e0) (desugar ["-", e1])
    _ -> undefined
desugar (SENum n) = JNum n
desugar (SESym s) = undefined

checkJExpr :: JExpr -> Integer -> Bool
checkJExpr expr ans = interp expr == ans

checkSExpr :: SExpr -> Integer -> Bool
checkSExpr expr = checkJExpr (desugar expr)

-- [(program, expected_answer)]
tests :: [(SExpr, Integer)]
tests = [ (1, 1)
        , (-1, -1)
        , (["+", 1, 1], 2)
        , (["*", 2, 3], 6)
        , (["*", -1, 3], -3)
        , (["*", ["+", 1, 10], 3], 33)
        , (["*", ["+", 1, -1], 3], 0)
        , (["+", 1, -1, 3], 3)
        , (["+", ["*", 1, -1], 3], 2)
        , (["*", ["+", 5, 10, -1], 2], 28)
        , (["*", 2, 2, 2, 2], 16)
        , (["*", ["+", 10, 10], ["*", 2, 2]], 80)
        , (["-", 3], -3)
        , (["-", 10, 20], -10)
        , (["-", ["+", 5, 10]], -15)
        , (["-", ["+", 5, 10], ["-", 3, 2]], 14)
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
