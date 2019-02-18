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

buildTypeUnificator :: Tree -> Set.Set String -> Map.Map String String -> (UnificatorPair, (Set.Set String, Map.Map String String))
buildTypeUnificator (Var x) usedVarsNames clojMap  =
        let varType     = Map.lookup x clojMap
        in
        unpackType varType
        where
            unpackType (Just varType) = (UnificatorPair EmptyContext (VarStatement varType), (usedVarsNames, clojMap))
            unpackType Nothing        = 
                let newUsedVars = Set.insert x usedVarsNames
                    newVarName  = setNewName ("a" ++ x) usedVarsNames
                in
                (UnificatorPair EmptyContext (VarStatement newVarName), (Set.insert newVarName newUsedVars, Map.insert x newVarName clojMap))
buildTypeUnificator (ApplicationTree p q) usedVarsNames clojMap  = 
        let pResult         = buildTypeUnificator p usedVarsNames clojMap
            qResult         = buildTypeUnificator q (fst $ snd pResult) (snd $ snd pResult)
            updatedUsedVars = fst $ snd qResult
            newVarName      = setNewName ("a'") updatedUsedVars
            pType           = getVarType $ fst pResult
            qType           = getVarType $ fst qResult
            newUsedVars     = Set.insert newVarName updatedUsedVars 
        in
        (UnificatorPair 
            (uniteContexts (getContext $ fst pResult) (getContext $ fst qResult) (Equation pType (ImplicationStatement qType (VarStatement newVarName))))
            (VarStatement newVarName),  (newUsedVars, Map.union (snd $ snd pResult) (snd $ snd qResult)))
buildTypeUnificator (LambdaTree (Var x) p) usedVarsNames clojMap = 
        let newUsedVars = Set.insert x usedVarsNames
            newVarName  = setNewName ("a" ++ x) newUsedVars
            pResult     = buildTypeUnificator p (Set.insert newVarName newUsedVars) (Map.insert x newVarName clojMap)
        in
        (UnificatorPair (getContext $ fst pResult) (ImplicationStatement (VarStatement newVarName) (getVarType $ fst pResult)),  (fst $ snd pResult, snd $ snd pResult))
       


buildExprTypeTemplate :: Tree -> Set.Set String -> Map.Map String String -> (Statement, (Set.Set String, Map.Map String String))
buildExprTypeTemplate (Var x) usedVarsNames clojMap =
        let varType = Map.lookup x clojMap
        in
        unpackType varType
        where
            unpackType (Just varType) = (VarStatement varType, (usedVarsNames, clojMap))
            unpackType Nothing        = 
                let newUsedVars = Set.insert x usedVarsNames
                    newVarName  = setNewName ("a" ++ x) newUsedVars
                in
                (VarStatement newVarName, (Set.insert newVarName newUsedVars, Map.insert x newVarName clojMap))
buildExprTypeTemplate (ApplicationTree p q) usedVarsNames clojMap  = 
        let pResult         = buildExprTypeTemplate p usedVarsNames clojMap
            qResult         = buildExprTypeTemplate q (fst $ snd pResult) (snd $ snd pResult)
            updatedUsedVars = fst $ snd qResult
            newVarName      = setNewName ("a'") updatedUsedVars
            newUsedVars     = Set.insert newVarName updatedUsedVars 
        in
        (VarStatement newVarName, (newUsedVars, Map.union (snd $ snd pResult) (snd $ snd qResult)))
buildExprTypeTemplate (LambdaTree (Var x) p) usedVarsNames clojMap = 
        let newUsedVars = Set.insert x usedVarsNames
            newVarName  = setNewName ("a" ++ x) newUsedVars
            pResult     = buildExprTypeTemplate p (Set.insert newVarName newUsedVars) (Map.insert x newVarName clojMap)
        in
        (ImplicationStatement (VarStatement newVarName) (fst pResult), (fst $ snd pResult, snd $ snd pResult))


getTypeInferenceStep :: Int -> TypeInferenceContext -> TypePair -> Int -> String
getTypeInferenceStep innerLevel tiContext exprTypePair ruleNum = 
    getInferencePrefix innerLevel ++ (showTypeInferenceContext $ Set.toList tiContext) ++ "|- " ++ show exprTypePair ++ " [rule #" ++ show ruleNum ++ "]" 

buildTypeInference :: Tree -> Map.Map Statement Statement -> TypeInferenceContext -> Int -> Set.Set String -> Map.Map String String -> ([String], (Set.Set String, Map.Map String String))
buildTypeInference expr@(LambdaTree var@(Var x) p) vtMap tiContext innerLevel usedVarsNames clojMap = 
    let varTypeTemplate = buildExprTypeTemplate var usedVarsNames clojMap
        typeTemplate    = buildExprTypeTemplate expr (fst $ snd varTypeTemplate) (snd $ snd varTypeTemplate)
        exprTypePair    = TypePair expr (substituteTypes (fst $ typeTemplate) vtMap)
        xTypePair       = TypePair var (substituteTypes (fst $ varTypeTemplate) vtMap)
        pTypeInf        = buildTypeInference p vtMap (Set.insert xTypePair tiContext) (innerLevel + 1) (fst $ snd varTypeTemplate) (snd $ snd varTypeTemplate)
    in
    (getTypeInferenceStep innerLevel tiContext exprTypePair 3 : (fst pTypeInf), (fst $ snd pTypeInf, snd $ snd pTypeInf))
buildTypeInference expr@(ApplicationTree p q) vtMap tiContext innerLevel usedVarsNames clojMap     =
    let typeTemplate = buildExprTypeTemplate expr usedVarsNames clojMap
        pTypeInf     = buildTypeInference p vtMap tiContext (innerLevel + 1) usedVarsNames clojMap
        qTypeInf     = buildTypeInference q vtMap tiContext (innerLevel + 1) (fst $ snd pTypeInf) (snd $ snd pTypeInf)
        newUsedVars =  fst $ snd qTypeInf
        exprTypePair = TypePair expr (substituteTypes (fst $ typeTemplate) vtMap)
    in 
    (getTypeInferenceStep innerLevel tiContext exprTypePair 2 
        : (fst pTypeInf ++ fst qTypeInf ), (newUsedVars, Map.union (snd $ snd pTypeInf) (snd $ snd qTypeInf)))
buildTypeInference expr@(Var x) vtMap tiContext innerLevel usedVarsNames clojMap                   =
    let varTypeTemplate = buildExprTypeTemplate expr usedVarsNames clojMap
        varTypePair     = TypePair expr (substituteTypes (fst $ varTypeTemplate) vtMap)
    in
     (getTypeInferenceStep innerLevel (Set.insert varTypePair tiContext) varTypePair 1 : [], ((fst $ snd varTypeTemplate), (snd $ snd varTypeTemplate))) 
           

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


getInferencePrefix :: Int -> String
getInferencePrefix innerLevel = concat $ take innerLevel (repeat "*   ") 

getFreeVars :: Tree -> Set.Set String -> Map.Map String String -> (Set.Set (String, String), (Set.Set String, Map.Map String String))
getFreeVars (LambdaTree (Var x) p) usedVarsNames clojMap = 
    let newUsedVars = Set.insert x usedVarsNames
        newVarName  = setNewName ("a" ++ x) newUsedVars
        pResult     = getFreeVars p (Set.insert newVarName newUsedVars) (Map.insert x newVarName clojMap)
    in
    (Set.delete (x, newVarName) (fst pResult), (fst $ snd pResult, snd $ snd pResult))
getFreeVars (ApplicationTree p q) usedVarsNames clojMap =
    let pVars = getFreeVars p usedVarsNames clojMap
        qVars = getFreeVars q (fst $ snd pVars) (snd $ snd pVars)
    in 
    (Set.union (fst pVars) (fst qVars), (fst $ snd qVars, Map.union (snd $ snd pVars) (snd $ snd qVars)))
getFreeVars (Var x) usedVarsNames clojMap              = 
    let varType = Map.lookup x clojMap
    in
    unpackType varType
    where
        unpackType (Just varType) = (Set.singleton (x, varType), (usedVarsNames, clojMap))
        unpackType Nothing        = 
            let newUsedVars = Set.insert x usedVarsNames
                newVarName  = setNewName ("a" ++ x) newUsedVars
            in
            (Set.singleton (x, newVarName), (Set.insert newVarName newUsedVars, Map.insert x newVarName clojMap))

buildInferenceContext :: Tree -> Map.Map Statement Statement -> TypeInferenceContext
buildInferenceContext expr vtMap = 
    let freeVars = Set.toList $ fst $ getFreeVars expr Set.empty Map.empty
    in
    Set.fromList $ construct freeVars vtMap
    where
        construct [] _           = []
        construct ((x,tp) : xs) vtMap = (TypePair (Var x) (substituteTypes (VarStatement tp) vtMap)) : construct xs vtMap

typing :: Tree -> String 
typing expr = 
    let unifPair          = fst $ buildTypeUnificator expr Set.empty Map.empty
        solvedSystem      = solveSystem $ getContext $ unifPair
    in
    -- show $ getContext $ unifPair
    buildTypeInferenceOrReturnNoTypeString solvedSystem (getVarType unifPair)
    where
        buildTypeInferenceOrReturnNoTypeString (Just solvedSystem) exprType = 
            let varsTypesMap      = buildVarTypesMap (getEquations solvedSystem) Map.empty
                resultedType      = substituteTypes exprType varsTypesMap
                inferenceContext  = buildInferenceContext expr varsTypesMap 
                typeInference     = buildTypeInference expr varsTypesMap inferenceContext 0 Set.empty Map.empty
            in
            -- show inferenceContext 
            unlines $ fst typeInference
            -- show solvedSystem ++ " " ++ show resultedType
        buildTypeInferenceOrReturnNoTypeString Nothing _                     = "Expression has no type\n"

main::IO()
main = do 
  input <- getLine
  case parseExpr (alexScanTokens input) of
    Left err   -> putStrLn err
    Right expr -> putStr $ typing expr