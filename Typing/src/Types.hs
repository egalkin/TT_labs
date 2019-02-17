module Types where

import Grammar (Tree (..))
import qualified Data.Set as Set

data Context = Context [Equation]
             | EmptyContext  
             | InvalidContext

instance Show Context where
    show (Context eqs) = show eqs
    show EmptyContext  = "{}"

data Equation = Equation Statement Statement

instance Show Equation where
    show (Equation s1 s2) = "{" ++ show s1 ++ "=" ++ show s2 ++ "}"

instance Eq Equation where
    eq1 == eq2 = show eq1 == show eq2

instance Ord Equation where
    compare eq1 eq2 = compare (show eq1) (show eq2)

data Statement = VarStatement String 
               | ImplicationStatement Statement Statement deriving (Eq, Ord)


type TypeInferenceContext = Set.Set TypePair


data TypePair = TypePair Tree Statement

instance Eq TypePair where
    p1 == p2 = show p1 == show p2

instance Ord TypePair where
    compare p1 p2 = compare (show p1) (show p2)

instance Show TypePair where
    show (TypePair tree typeStat) = show tree ++ " : " ++ show typeStat
 
instance Show Statement where
    show (VarStatement var) = var
    -- show (ImplicationStatement var1 var2) = "->" ++ "(" ++ show var1  ++ " " ++ show var2 ++ ")"              
    show (ImplicationStatement var1 var2) = "(" ++ show var1  ++ "->" ++ show var2 ++ ")"              


data UnificatorPair = UnificatorPair Context Statement 

instance Show UnificatorPair where
    show (UnificatorPair cnt tp) = show cnt ++ " " ++ show tp