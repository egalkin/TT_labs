module Main where


import Grammar (Tree (..))
import Types 
import Lexer (alexScanTokens)
import Parser (parseExpr)
import Data.List (elemIndex)
import qualified Data.Set as Set
import qualified Data.Map as Map

setNewName :: String -> Set.Set String -> String
setNewName newName usedVarsNames  
    | not (Set.member newName usedVarsNames) = newName
    | otherwise                              = setNewName (newName ++ "'") usedVarsNames


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

substitutionStep :: Statement -> Statement -> Equation -> Equation
substitutionStep a omega curEqu@(Equation stat1 stat2) = Equation (statementSubstitution a omega stat1) (statementSubstitution a omega stat2) 

substitute :: Statement -> Statement -> [Equation] -> [Equation]
substitute _ _ []           = []
substitute a omega (x : xs) = substitutionStep a omega x : substitute a omega xs

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
    | otherwise                                                                              = doUnification (substitute a omega xs) ++ [equ]
unificationStep equ@(Equation a@(VarStatement var) omega) xs                                 = doUnification (substitute a omega xs) ++ [equ]
    


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
            fallOrContinue True solvedContext              = Nothing
            fallOrContinue False solvedContext = 
                let solved = isSolved solvedContext (Set.fromList $ countAllMetVars $ solvedContext)
                in 
                returnOrContinue solvedContext solved
                where 
                   returnOrContinue solvedContext True        = Just (Context  solvedContext)
                   returnOrContinue solvedContext False       = systemSolvingLoop (Context solvedContext) (cnt+1)
systemSolvingLoop _ _ = Just EmptyContext

solveSystem :: Context -> Maybe Context
solveSystem cont = systemSolvingLoop cont 0

buildTypeUnificator :: Tree -> Set.Set String -> Int -> (UnificatorPair, (Int, Set.Set String))
buildTypeUnificator (Var x) usedVarsNames num = 
    let newUsedVars = (Set.insert x usedVarsNames)
        newVarName  = setNewName ("a" ++ show num ++ x) newUsedVars
    in
    (UnificatorPair EmptyContext (VarStatement newVarName), (num, Set.insert newVarName newUsedVars))
buildTypeUnificator (ApplicationTree p q) usedVarsNames num = 
        let pResult         = buildTypeUnificator p usedVarsNames (num+1)
            qResult         = buildTypeUnificator q usedVarsNames ((fst $ snd pResult) + 1)
            updatedUsedVars = Set.union (snd $ snd pResult) (snd $ snd qResult)
            newVarName      = setNewName ("a" ++ show (fst $ snd qResult) ++ "'") updatedUsedVars
            pType           = getVarType $ fst pResult
            qType           = getVarType $ fst qResult
            newUsedVars     = Set.insert newVarName updatedUsedVars 
        in
        (UnificatorPair 
            (uniteContexts (getContext $ fst pResult) (getContext $ fst qResult) (Equation pType (ImplicationStatement qType (VarStatement newVarName))))
            (VarStatement newVarName), (fst $ snd qResult, newUsedVars))
buildTypeUnificator (LambdaTree (Var x) p) usedVarsNames num = 
        let pResult    = buildTypeUnificator p usedVarsNames num
            newVarName = "a" ++ show num ++ x
        in
        (UnificatorPair (getContext $ fst pResult) (ImplicationStatement (VarStatement newVarName) (getVarType $ fst pResult)),(num, usedVarsNames))

buildExprTypeTemplate :: Tree -> Set.Set String  -> Int-> (Statement, (Int, Set.Set String))
buildExprTypeTemplate (Var x) usedVarsNames num = 
    let newUsedVars = (Set.insert x usedVarsNames)
        newVarName = setNewName ("a" ++ show num ++ x) newUsedVars
    in
    (VarStatement newVarName, (num, Set.insert newVarName newUsedVars))
buildExprTypeTemplate (ApplicationTree p q) usedVarsNames num = 
        let pResult         = buildExprTypeTemplate p usedVarsNames (num + 1)
            qResult         = buildExprTypeTemplate q usedVarsNames ((fst $ snd pResult) + 1)
            updatedUsedVars = Set.union (snd $ snd pResult) (snd $ snd qResult)
            newVarName      = setNewName ("a" ++ show (fst $ snd qResult) ++ "'") updatedUsedVars
            newUsedVars     = Set.insert newVarName updatedUsedVars 
        in
        (VarStatement newVarName, (fst $ snd qResult, newUsedVars))       
buildExprTypeTemplate (LambdaTree (Var x) p) usedVarsNames num = 
        let pResult    = buildExprTypeTemplate p usedVarsNames num
            newVarName = "a" ++ show num ++  x
        in
        (ImplicationStatement (VarStatement newVarName) (fst pResult), (num, usedVarsNames))

getContext :: UnificatorPair -> Context
getContext (UnificatorPair cont varName) =  cont

getVarType :: UnificatorPair -> Statement 
getVarType (UnificatorPair cont statement) = statement

getEquations :: Context -> [Equation]
getEquations (Context eqs)  = eqs
getEquations EmptyContext   = []

buildVarTypesMap :: [Equation] -> Map.Map Statement Statement -> Map.Map Statement Statement
buildVarTypesMap [] varsTypesMap                            = varsTypesMap
buildVarTypesMap ((Equation stat1 stat2) : xs) varsTypesMap = 
    let updatedMap = Map.insert stat1 stat2 varsTypesMap
    in
    buildVarTypesMap xs updatedMap

substituteTypes :: Statement -> Map.Map Statement Statement -> Statement
substituteTypes (ImplicationStatement stat1 stat2) vtMap = ImplicationStatement (substituteTypes stat1 vtMap) (substituteTypes stat2 vtMap)
substituteTypes var@(VarStatement x) vtMap               =
    let possibleTypeVar = Map.lookup var vtMap
    in
    updateTypeOrReturnPrev possibleTypeVar
    where
        updateTypeOrReturnPrev (Just a) = a
        updateTypeOrReturnPrev Nothing  = var

showTypeInferenceContext :: [TypePair] -> String
showTypeInferenceContext []       = []
showTypeInferenceContext (x : []) = show x ++ " "
showTypeInferenceContext (x : xs) = show x ++ ", " ++ showTypeInferenceContext xs

getTypeInferenceStep :: Int -> TypeInferenceContext -> TypePair -> Int -> String
getTypeInferenceStep innerLevel tiContext exprTypePair ruleNum = 
    getInferencePrefix innerLevel ++ (showTypeInferenceContext $ Set.toList tiContext) ++ "|- " ++ show exprTypePair ++ " [rule #" ++ show ruleNum ++ "]" 

buildTypeInference :: Tree -> Map.Map Statement Statement -> TypeInferenceContext -> Int -> Int -> (Int, [String])
buildTypeInference expr@(LambdaTree var@(Var x) p) vtMap tiContext innerLevel num = 
    let typeTemplate = buildExprTypeTemplate expr Set.empty num
        exprTypePair = TypePair expr (substituteTypes (fst $ typeTemplate) vtMap)
        xTypePair    = TypePair var (substituteTypes (VarStatement ("a" ++ show num ++ x)) vtMap)
        pTypeInf     = buildTypeInference p vtMap (Set.insert xTypePair tiContext) (innerLevel + 1) num
    in
    (num, getTypeInferenceStep innerLevel tiContext exprTypePair 3 : (snd pTypeInf))
buildTypeInference expr@(ApplicationTree p q) vtMap tiContext innerLevel num      =
    let typeTemplate = buildExprTypeTemplate expr Set.empty num
        exprTypePair = TypePair expr (substituteTypes (fst $ typeTemplate) vtMap)
        pTypeInf     = buildTypeInference p vtMap tiContext (innerLevel + 1) (num + 1)
        qTypeInf     = buildTypeInference q vtMap tiContext (innerLevel + 1) ((fst pTypeInf) + 1)
    in 
    (fst qTypeInf, getTypeInferenceStep innerLevel tiContext exprTypePair 2 
        : (snd pTypeInf ++ snd qTypeInf ))
buildTypeInference expr@(Var x) vtMap tiContext innerLevel num                    =
    let exprTypePair = TypePair expr (substituteTypes (VarStatement ("a" ++ show num ++ x)) vtMap) 
    in 
    (num, getTypeInferenceStep innerLevel (Set.insert exprTypePair tiContext) exprTypePair 1 : [])

    
getInferencePrefix :: Int -> String
getInferencePrefix innerLevel = concat $ take innerLevel (repeat "*   ") 

getFreeVars :: Tree -> Int -> (Int, Set.Set (String, Int))
getFreeVars (LambdaTree (Var x) p) num = (num, Set.delete (x, num) (snd $ getFreeVars p num))
getFreeVars (ApplicationTree p q)  num =
    let pVars = getFreeVars p (num + 1)
        qVars = getFreeVars q (fst pVars)
    in 
    (fst qVars, Set.union (snd pVars) (snd qVars))
getFreeVars (Var x) num               = (num, Set.singleton (x, num))

buildInferenceContext :: Tree -> Map.Map Statement Statement -> TypeInferenceContext
buildInferenceContext expr vtMap = 
    let freeVars = Set.toList $ snd $ getFreeVars expr 0
    in
    Set.fromList $ construct freeVars vtMap
    where
        construct [] _           = []
        construct ((x,num) : xs) vtMap = (TypePair (Var x) (substituteTypes (VarStatement ("a" ++ show num ++  x)) vtMap)) : construct xs vtMap

typing :: Tree -> String 
typing expr = 
    let unifPair          = fst $ buildTypeUnificator expr Set.empty 0
        solvedSystem      = solveSystem $ getContext $ unifPair
    in
    buildTypeInferenceOrReturnNoTypeString solvedSystem (getVarType unifPair)
    where
        buildTypeInferenceOrReturnNoTypeString (Just solvedSystem) exprType = 
            let varsTypesMap      = buildVarTypesMap (getEquations solvedSystem) Map.empty
                resultedType      = substituteTypes exprType varsTypesMap
                inferenceContext  = buildInferenceContext expr varsTypesMap 
                typeInference     = buildTypeInference expr varsTypesMap inferenceContext 0 0
            in
            -- show inferenceContext 
            unlines $ snd typeInference
            -- show solvedSystem
        buildTypeInferenceOrReturnNoTypeString Nothing _                     = "Expression has no type"

main::IO()
main = do 
  input <- getLine
  case parseExpr (alexScanTokens input) of
    Left err   -> putStrLn err
    Right expr -> putStr $ typing expr