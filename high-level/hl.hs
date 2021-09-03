data J0Expr = J0Num Integer | J0Plus J0Expr J0Expr | J0Mult J0Expr J0Expr

j0pp :: J0Expr -> String
j0pp (J0Num n) = show n
j0pp (J0Plus lhs rhs) = "(+ " ++ j0pp lhs ++ " " ++ j0pp rhs ++ ")"
j0pp (J0Mult lhs rhs) = "(* " ++ j0pp lhs ++ " " ++ j0pp rhs ++ ")"

main :: IO ()
main = putStrLn $ j0pp $ J0Plus (J0Num 1) (J0Mult (J0Num 2) (J0Num 3))
