data J0Expr = J0Num Integer | J0Plus J0Expr J0Expr | J0Mult J0Expr J0Expr

j0pp :: J0Expr -> String
j0pp (J0Num n) = show n
j0pp (J0Plus lhs rhs) = "(+ " ++ j0pp lhs ++ " " ++ j0pp rhs ++ ")"
j0pp (J0Mult lhs rhs) = "(* " ++ j0pp lhs ++ " " ++ j0pp rhs ++ ")"

-- [(program, expected_answer)]
j0tests :: [(J0Expr, Integer)]
j0tests = [ (J0Num 1, 1)
          , (J0Num (-1), -1)
          , (J0Plus (J0Num 1) (J0Num 1), 2)
          , (J0Mult (J0Num 2) (J0Num 3), 6)
          , (J0Mult (J0Num (-1)) (J0Num 3), -3)
          , (J0Mult (J0Plus (J0Num 1) (J0Num 10)) (J0Num 3), 33)
          , (J0Mult (J0Plus (J0Num 1) (J0Num (-1))) (J0Num 3), 0)
          , (J0Plus (J0Plus (J0Num 1) (J0Num (-1))) (J0Num 3), 3)
          , (J0Plus (J0Mult (J0Num 1) (J0Num (-1))) (J0Num 3), 2)
          , (J0Mult (J0Plus (J0Plus (J0Num 5) (J0Num 10)) (J0Num (-1))) (J0Num 2), 28)
          , (J0Mult (J0Mult (J0Mult (J0Num 2) (J0Num 2)) (J0Num 2)) (J0Num 2), 16)
          , (J0Mult (J0Plus (J0Num 10) (J0Num 10)) (J0Mult (J0Num 2) (J0Num 2)), 80) ]

j0interp :: J0Expr -> Integer
j0interp (J0Num n) = n
j0interp (J0Plus lhs rhs) = j0interp lhs + j0interp rhs
j0interp (J0Mult lhs rhs) = j0interp lhs * j0interp rhs

j0check :: J0Expr -> Integer -> Bool
j0check expr ans = j0interp expr == ans

j0runTask3Tests :: IO ()
j0runTask3Tests = do
    let testResults = map (uncurry j0check) j0tests
    let numSuccesses = length $ filter id testResults
    let numFailures = length j0tests - numSuccesses
    putStrLn $ show numSuccesses ++ " successes and " ++ show numFailures ++ " failures"

main :: IO ()
main = j0runTask3Tests
