-- For SExpr overloading
{-# LANGUAGE OverloadedStrings, OverloadedLists, TypeFamilies #-}

-- For SExpr overloading
import GHC.Exts (IsList(..))
import Data.String (IsString(..))

data JExpr = JNum Integer | JPlus JExpr JExpr | JMult JExpr JExpr

data SExpr = SESym String | SENum Integer | SEList [SExpr] deriving (Show, Eq)

pp :: JExpr -> String
pp (JNum n) = show n
pp (JPlus lhs rhs) = "(+ " ++ pp lhs ++ " " ++ pp rhs ++ ")"
pp (JMult lhs rhs) = "(* " ++ pp lhs ++ " " ++ pp rhs ++ ")"

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
        , (["*", ["+", 10, 10], ["*", 2, 2]], 80) ]

interp :: JExpr -> Integer
interp (JNum n) = n
interp (JPlus lhs rhs) = interp lhs + interp rhs
interp (JMult lhs rhs) = interp lhs * interp rhs

check :: JExpr -> Integer -> Bool
check expr ans = interp expr == ans

runTests :: IO ()
runTests = do
    let testJExprs = error "desugar implemented in next commit"
    let testResults = map (uncurry check) testJExprs
    let numSuccesses = length $ filter id testResults
    let numFailures = length tests - numSuccesses
    putStrLn $ show numSuccesses ++ " successes and " ++ show numFailures ++ " failures"

main :: IO ()
main = runTests

-- Enable conversion from number literals into SENum
-- Only fromInteger is needed so the rest is left undefined
instance Num SExpr where
    fromInteger = SENum
    (+) = undefined
    (*) = undefined
    (-) = undefined
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
