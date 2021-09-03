data J0Expr = J0Num Integer | J0Plus J0Expr J0Expr | J0Mult J0Expr J0Expr

main :: IO ()
main = putStrLn "Hello"
