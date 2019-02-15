module Grammar where

data Tree = LambdaTree Tree Tree 
          | ApplicationTree Tree Tree
          | Var String 


instance Show Tree where
    show (LambdaTree perem body) = "(\\" ++ show perem ++ "." ++ show body ++ ")"
    show (ApplicationTree a b)   = "(" ++ show a ++ " " ++ show b ++ ")"
    show (Var name)              = name 