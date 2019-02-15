module Main where


import Grammar (Tree (..))
import Types 
import Lexer (alexScanTokens)
import Parser (parseExpr)
import Data.List (elemIndex)
import qualified Data.Set as Set
import qualified Data.Map.Lazy as Map

setNewName :: String -> Set.Set String -> String
setNewName newName usedVarsNames  
    | not (Set.member newName usedVarsNames) = newName
    | otherwise                              = setNewName (newName ++ "'") usedVarsNames


getContext :: UnificatorPair -> Context
getContext (UnificatorPair cont varName) =  cont

getVarType :: UnificatorPair -> Statement 
getVarType (UnificatorPair cont statement) = statement


uniteContexts :: Context -> Context -> Equation -> Context
uniteContexts EmptyContext (Context eqs) eq    = Context (eq : eqs)
uniteContexts (Context eqs) EmptyContext eq    = Context (eq : eqs)
uniteContexts (Context eqs1) (Context eqs2) eq = Context (eq : (eqs1 ++ eqs2))
uniteContexts EmptyContext EmptyContext eq     = Context [eq]

statementSubstitution :: Statement -> Statement -> Statement -> Statement
statementSubstitution a omega (ImplicationStatement lp rp) =
    ImplicationStatement (statementSubstitution a omega lp) (statementSubstitution a omega rp)
statementSubstitution a omega curVar@(VarStatement var) 
    | a == curVar                                          = omega
    | otherwise                                            = curVar

substitutionStep :: Equation -> Statement -> Statement -> Equation -> Equation
substitutionStep equ a omega curEqu@(Equation stat1 stat2)
    | equ /= curEqu = Equation (statementSubstitution a omega stat1) (statementSubstitution a omega stat2) 
    | otherwise     = equ

substitute :: Equation -> Statement -> Statement -> [Equation] -> [Equation]
substitute _ _ _ []           = []
substitute equ a omega (x : xs) = substitutionStep equ a omega x : substitute equ a omega xs

unificationStep :: Equation -> [Equation] -> [Equation]
unificationStep (Equation (ImplicationStatement lp rp) (VarStatement var)) xs                 = 
    let res = (Equation (VarStatement var) (ImplicationStatement lp rp))
    in
    doUnification xs ++ [res]
unificationStep (Equation (ImplicationStatement lp1 rp1) (ImplicationStatement lp2 rp2)) xs   = 
    let res = [Equation lp1 lp2, Equation rp1 rp2]
    in
    doUnification xs ++ res
unificationStep equ@(Equation a@(VarStatement x) omega@(VarStatement y)) xs 
    | x == y                                                                                 = doUnification xs
    | otherwise                                                                              = doUnification (substitute equ a omega xs) ++ [equ]
unificationStep equ@(Equation a@(VarStatement var) omega) xs                                 = doUnification (substitute equ a omega xs) ++ [equ]
    


doUnification :: [Equation] -> [Equation]
doUnification []        = []
doUnification (x : xs)  = unificationStep x xs 


countMetVars :: Statement -> [String]
countMetVars (ImplicationStatement lp rp) = countMetVars lp ++ countMetVars rp
countMetVars (VarStatement var)           = [var]

countEqMetVars :: Equation -> [String]
countEqMetVars (Equation stat1 stat2) =  countMetVars stat2

countAllMetVars :: [Equation] -> [String]
countAllMetVars []       = []
countAllMetVars (x : xs) = countEqMetVars x ++ countAllMetVars xs

isAppropriate :: Equation -> Set.Set String -> (Bool, Set.Set String)
isAppropriate (Equation (VarStatement x) rp ) alreadyMet 
    | not (Set.member x alreadyMet)  = (True, Set.insert x alreadyMet)
    | otherwise                             = (False, alreadyMet)
isAppropriate _  alreadyMet          = (False, alreadyMet)


isSolved :: [Equation] -> Set.Set String -> Bool 
isSolved [] _ = True
isSolved (x : xs) alreadyMet = 
    let apprResult        = isAppropriate x alreadyMet

        xAppr             = fst apprResult
        updatedAlreadyMet = snd apprResult
    in 
    returnOrContinue xAppr xs updatedAlreadyMet
    where 
        returnOrContinue True xs updatedAlreadyMet = isSolved xs updatedAlreadyMet
        returnOrContinue False _ _                 = False 


isEntered :: Statement -> Statement -> Bool 
isEntered a (ImplicationStatement lp rp) = isEntered a lp || isEntered a rp
isEntered a curVar@(VarStatement x)      = a == curVar

isIncompatibleEquation :: Equation -> Bool
isIncompatibleEquation (Equation a@(VarStatement x) impl@(ImplicationStatement lp rp)) =
    isEntered a impl
isIncompatibleEquation _                                                               = False

isIncompatible :: [Equation] -> Bool 
isIncompatible [] = False
isIncompatible (x : xs) =
    let xInc = isIncompatibleEquation x
    in
    returnOrContinue xInc x xs
    where
        returnOrContinue False x xs = isIncompatible xs
        returnOrContinue True _ _   = True

systemSolvingLoop :: Context -> Int -> Maybe Context
systemSolvingLoop (Context eqs) cnt = 
        let solvedContext = doUnification eqs
            incompatible  = isIncompatible solvedContext
            in
            fallOrContinue incompatible solvedContext
            where 
                fallOrContinue True _              = Nothing
                fallOrContinue False solvedContext = 
                    let solved = isSolved solvedContext (Set.fromList $ countAllMetVars $ solvedContext)
                    in 
                    returnOrContinue solvedContext solved
                    where 
                       returnOrContinue solvedContext True        = Just (Context  solvedContext)
                       returnOrContinue solvedContext False       = systemSolvingLoop (Context solvedContext) (cnt+1)
systemSolvingLoop _ _ = Just EmptyContext

solveSystem :: Context -> Context
solveSystem cont =
    let systemSolution = systemSolvingLoop cont 0
    in
    getResult systemSolution
    where
        getResult (Just a) = a
        getResult Nothing  = InvalidContext


buildTypeUnificator :: Tree -> Set.Set String -> (UnificatorPair, Set.Set String)
buildTypeUnificator (Var x) usedVarsNames = 
    let newUsedVars = (Set.insert x usedVarsNames)
        newVarName = setNewName ("a" ++ x) newUsedVars
        in
        (UnificatorPair EmptyContext (VarStatement newVarName), Set.insert newVarName newUsedVars)
buildTypeUnificator (ApplicationTree p q) usedVarsNames = 
        let pResult         = buildTypeUnificator p usedVarsNames
            qResult         = buildTypeUnificator q usedVarsNames
            updatedUsedVars = Set.union (snd pResult) (snd qResult)
            newVarName      = setNewName ("a" ++ "'") updatedUsedVars
            pType           = getVarType $ fst pResult
            qType           = getVarType $ fst qResult
            newUsedVars     = Set.insert newVarName updatedUsedVars 
            in
            (UnificatorPair 
                (uniteContexts (getContext $ fst pResult) (getContext $ fst qResult) (Equation pType (ImplicationStatement qType (VarStatement newVarName))))
                (VarStatement newVarName), newUsedVars)
buildTypeUnificator (LambdaTree (Var x) p) usedVarsNames = 
        let pResult    = buildTypeUnificator p usedVarsNames 
            newVarName = "a" ++ x
            in
            (UnificatorPair (getContext $ fst pResult) (ImplicationStatement (VarStatement newVarName) (getVarType $ fst pResult)), usedVarsNames)


typing :: Tree -> Context 
typing t =  solveSystem $ getContext $ fst $ buildTypeUnificator t Set.empty

main::IO()
main = do 
  input <- getLine
  case parseExpr (alexScanTokens input) of
    Left err   -> putStrLn err
    Right expr -> putStrLn $ show $ typing expr