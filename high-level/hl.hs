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
tests :: [(JExpr, Integer)]
tests = [ (JNum 1, 1)
        , (JNum (-1), -1)
        , (JPlus (JNum 1) (JNum 1), 2)
        , (JMult (JNum 2) (JNum 3), 6)
        , (JMult (JNum (-1)) (JNum 3), -3)
        , (JMult (JPlus (JNum 1) (JNum 10)) (JNum 3), 33)
        , (JMult (JPlus (JNum 1) (JNum (-1))) (JNum 3), 0)
        , (JPlus (JPlus (JNum 1) (JNum (-1))) (JNum 3), 3)
        , (JPlus (JMult (JNum 1) (JNum (-1))) (JNum 3), 2)
        , (JMult (JPlus (JPlus (JNum 5) (JNum 10)) (JNum (-1))) (JNum 2), 28)
        , (JMult (JMult (JMult (JNum 2) (JNum 2)) (JNum 2)) (JNum 2), 16)
        , (JMult (JPlus (JNum 10) (JNum 10)) (JMult (JNum 2) (JNum 2)), 80) ]

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
