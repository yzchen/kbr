import Data.List
import Data.Maybe

data Formula = Var    Char
            | Not     Formula
            | And     Formula Formula
            | Or      Formula Formula
            | Implies Formula Formula
            | ForAll  Char Formula
            | Exists  Char Formula
            deriving Eq

instance Show Formula where
    show a = case a of
        (Var     p)   -> [p]
        (Not     a)   -> "¬" ++ show a
        (And     a b) -> "(" ++ show a ++ " ∧ " ++ show b ++ ")"
        (Or      a b) -> "(" ++ show a ++ " ∨ " ++ show b ++ ")"
        (Implies a b) -> "(" ++ show a ++ " -> " ++ show b ++ ")"
        (ForAll  s ts) -> "∀" ++ [s] ++ " " ++ show ts
        (Exists  s ts) -> "∃" ++ [s] ++ " " ++ show ts

data Predicate = Predicate [Formula] [Formula] deriving Eq

instance Show Predicate where
  show (Predicate x y) = show x ++ " ⊢ " ++ show y

data Rule = Axiom | WL | WR | NL | NR | AL | AR | OL | OR | IL | IR | FL | FR | EL | ER deriving (Show, Eq)

data Node = Node Predicate Rule deriving (Show, Eq)

data Tree = Singleton {step::Node, next::Maybe Tree}
         | Branch {step::Node, first::Maybe Tree, second::Maybe Tree}
         | END
         deriving Eq

showTree :: Tree -> String
showTree = unlines . reverse . showTree'
    where showTree' node =
            case node of
                (Singleton (Node predicate rule) tree1) -> ["(" ++ show rule ++ ")" ++ show predicate] ++ (showTree' $ fromMaybe END tree1)
                (Branch (Node predicate rule) tree1 tree2) -> ["(" ++ show rule ++ ")" ++ show predicate] ++ (showTree' $ fromMaybe END tree1) ++ (showTree' $ fromMaybe END tree2)
                END -> [""]

getNot :: Formula -> Formula
getNot z = case z of
    Not x -> x
    y -> Not y

getComponents :: Formula -> (Formula, Formula)
getComponents z = case z of
            And x y -> (x, y)
            Or x y -> (x, y)
            Implies x y -> (x, y)

isNot :: Formula -> Bool
isNot (Not _) = True
isNot _       = False

isAnd :: Formula -> Bool
isAnd (And _ _) = True
isAnd _         = False

isOr :: Formula -> Bool
isOr (Or _ _) = True
isOr _        = False

isImp :: Formula -> Bool
isImp (Implies _ _) = True
isImp _ = False

isForAll :: Formula -> Bool
isForAll (ForAll _ _) = True
isForAll _ = False

isExists :: Formula -> Bool
isExists (Exists _ _) = True
isExists _ = False

removeForAll :: Formula -> Formula
removeForAll z@(ForAll qt a) = a

removeExists :: Formula -> Formula
removeExists z = case z of
    Exists _ a -> a

provable :: Tree -> Bool
provable tr = case tr of
    Singleton (Node _ r) n -> r == Axiom || tree1
        where tree1 = case n of
                Just x -> provable x
                _ -> False
    Branch (Node _ _) tree1 tree2 -> childTree tree1 && childTree tree2
        where childTree p = case p of
                Just x -> provable x
                _ -> False

printTree :: Tree -> String
printTree pf = if provable pf
        then showTree pf ++ "\n"
        else "False\n"

derivation :: Predicate -> Maybe Tree
derivation predicates@(Predicate gamma delta)
    | isInfixOf delta gamma =
        Just $ Singleton (Node predicates Axiom) Nothing
    | all (not . null) [gamma \\ delta, intersect gamma delta] =          -- WL
        let (x : _) = gamma \\ delta in
        Just $ Singleton (Node predicates WL) (derivation (Predicate (delete x gamma) delta))
    | all (not . null) [delta \\ gamma, intersect gamma delta] =          -- WR
        let (x : _) = delta \\ gamma in
        Just $ Singleton (Node predicates WR) (derivation (Predicate gamma (delete x delta)))
    | any isNot gamma =                                                   -- NL
        let (gammaNot,  gammaNoNot) = partition isNot gamma in
        Just $ Singleton (Node predicates NL) (derivation (Predicate gammaNoNot (delta ++ map getNot gammaNot)))
    | any isNot delta =                                                   -- NR
        let (deltaNot, deltaNoNot) = partition isNot delta in
        Just $ Singleton (Node predicates NR) (derivation (Predicate (gamma ++ map getNot deltaNot) deltaNoNot))
    | any isAnd gamma =                                                   -- AL
        let (gammaAnd,  gammaNoAnd) = partition isAnd gamma in
        Just $ Singleton (Node predicates AL) (derivation (Predicate (gammaNoAnd ++ concatMap (toList . getComponents) gammaAnd) delta))
    | any isAnd delta =                                                   -- AR
        let ((x : _), _) = partition isAnd delta in
        let (a, b) = getComponents x in
        let tree1 = Predicate gamma (a : delete x delta) in
        let tree2 = Predicate gamma (b : delete x delta) in
        Just $ Branch (Node predicates AR) (derivation tree1) (derivation tree2)
    | any isOr gamma =                                                    -- OL
        let ((x : _), _) = partition isOr gamma in
        let (a, b) = getComponents x in
        let tree1 = Predicate (a : delete x gamma) delta in
        let tree2 = Predicate (b : delete x gamma) delta in
        Just $ Branch (Node predicates OL) (derivation tree1) (derivation tree2)
    | any isOr delta =                                                    -- OR
        let (deltaOr, deltaNoOr) = partition isOr delta in
        Just $ Singleton (Node predicates OR) (derivation (Predicate gamma (deltaNoOr ++ concatMap (toList . getComponents) deltaOr)))
    | any isImp delta =                                                   -- IL
        let (deltaImp, deltaNoImp) = partition isImp delta in
        Just $ Singleton (Node predicates IR) (derivation (Predicate (gamma ++ map (fst . getComponents) deltaImp) (deltaNoImp ++ map (snd . getComponents) deltaImp)))
    | any isImp gamma =                                                   -- IR
        let ((x : _), _) = partition isImp gamma in
        let (a, b) = getComponents x in
        let tree1 = Predicate (delete x gamma) (a : delta) in
        let tree2 = Predicate (b : delete x gamma) delta in
        Just $ Branch (Node predicates IL) (derivation tree1) (derivation tree2)
    | any isForAll gamma =                                                  -- FL
        let ((x : _), _) = partition isForAll gamma in
        let a = removeForAll x in
        Just $ Singleton (Node predicates FL) (derivation (Predicate (a : delete x gamma) delta))
    | any isForAll delta =                                                  -- FR
        let ((x : _), _) = partition isForAll delta in
        let a = removeForAll x in
        Just $ Singleton (Node predicates FR) (derivation (Predicate gamma (a : delete x delta)))
    | otherwise = Nothing
    where toList (x, y) = [x, y]

main = do
    let p = Var 'p'
    let q = Var 'q'
    let r = Var 'r'

    let gamma1 = []
    let gamma2 = [q]
    let gamma3 = [Implies (And p q) r]

    let delta1 = [Implies p (Implies q p)]
    let delta2 = [Implies (Implies p (Implies q r)) (Implies (Implies p q) (Implies p r))]
    let delta3 = [Implies (Implies (Not q) (Not p)) (Implies p q)]
    let delta4 = [Implies p (Implies (Not p) q)]
    let delta5 = [Implies (Implies (Not p) p) p]
    let delta6 = [Implies (And (Implies p q) (p)) q]
    let delta7 = [Implies p q]
    let delta8 = [Implies p (Implies q r)]
    let delta9 = [Implies (ForAll 'x' p) p]
    let delta10 = [Implies (ForAll 'x' (Implies p q)) (Implies (ForAll 'x' p) (ForAll 'x' q))]
    let delta11 = [Implies p (ForAll 'x' p)]

    -- test predicate Hilbert Axioms
    putStrLn "Hilbert Axioms 1. ⊢ p -> (q -> p)"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta1
    putStrLn "Hilbert Axioms 2. ⊢ (p -> (q -> r)) -> ((p -> q) -> (p -> r))"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta2
    putStrLn "Hilbert Axioms 3. ⊢ (¬q -> ¬p) -> (p -> q)"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta3
    putStrLn "Hilbert Axioms 4. ⊢ p -> (¬p -> q)"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta4
    putStrLn "Hilbert Axioms 5. ⊢ (¬p -> p) -> p"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta5

    -- test modus ponens
    putStrLn "Modus Ponens : ⊢ ((p -> q) ∧ p) -> q"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta6

    -- other examples
    putStrLn "Example : ⊢ p -> q"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta7
    putStrLn "Example : p ⊢ p -> q"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma2 delta7
    putStrLn "Example : (p & q) -> r ⊢ p -> (q -> r)"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma3 delta8

    -- test L1 Hilbert Axioms
    putStrLn "Hilbert Axioms 6. ⊢ (∀x p) -> p[x/t]"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta9
    putStrLn "Hilbert Axioms 7. ⊢ (∀x (p -> q)) -> (∀x p -> ∀x q)"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta10
    putStrLn "Hilbert Axioms 8. ⊢ p -> ∀x p"
    putStrLn $ printTree $ fromJust $ derivation $ Predicate gamma1 delta11
