module Types where

import qualified Data.Set as Set

data Context = Context [Equation]
             | EmptyContext  
             | InvalidContext

instance Show Context where
    show (Context eqs) = show eqs
    show EmptyContext  = "{}"
    show InvalidContext = "InvalidContext"

data Equation = Equation Statement Statement

instance Show Equation where
    show (Equation s1 s2) = "{" ++ show s1 ++ "=" ++ show s2 ++ "}"

instance Eq Equation where
    eq1 == eq2 = show eq1 == show eq2

instance Ord Equation where
    compare eq1 eq2 = compare (show eq1) (show eq2)

data Statement = VarStatement String 
               | ImplicationStatement Statement Statement deriving Eq


instance Show Statement where
    show (VarStatement var) = var
    show (ImplicationStatement var1 var2) = "->" ++ "(" ++ show var1  ++ " " ++ show var2 ++ ")"              


data UnificatorPair = UnificatorPair Context Statement 

instance Show UnificatorPair where
    show (UnificatorPair cnt tp) = show cnt ++ " " ++ show tp