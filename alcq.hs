import Data.List
import Data.Maybe
import Data.Char
import Data.Ord

-- remove duplicates in list
rmDups :: Eq a => [a] -> [a]
rmDups = foldl (\seen x -> if x `elem` seen
                    then seen
                    else seen ++ [x]) []

-- join a string with a string seperator
strJoin sep arr = case arr of
            [] -> ""
            [x] -> [x]
            (x : xs) -> [x] ++ sep ++ strJoin sep xs

-- distinct combinations in list
pairs :: [a] -> [(a, a)]
pairs xs = [(x1, x2) | (x1:xs1) <- tails xs, x2 <- xs1]

data Formula = Unary   Char [Char]              -- key definition
            | Not     Formula
            | And     Formula Formula
            | Or      Formula Formula
            | Relation Char Char Char
            | ForAll  Char Formula Char         -- need instance to specify which instance corresponds to this formula
            | Exists  Char Formula Char
            | GTEnr   Int Char Formula Char     -- last char same as forall, exists
            | LTEnr   Int Char Formula Char
            | SubSumption Formula Formula
            | Equals Formula Formula            -- Formula without instances
            | Distinction Char Char             -- used in number restrictions
            deriving Eq

instance Show Formula where
    show f = case f of
            (Unary   f x) -> [f] ++ "(" ++ (strJoin "," x) ++  ")"
            (Not     a)   -> "¬" ++ show a
            (And     a b) -> "(" ++ show a ++ " ⊓ " ++ show b ++ ")"
            (Or      a b) -> "(" ++ show a ++ " ⊔ " ++ show b ++ ")"
            (Relation r x y) -> [r] ++ "("++ [x] ++ "," ++ [y] ++ ")"
            (ForAll  s ts x) -> "∀" ++ [s] ++ "." ++ show ts ++ "(" ++ [x] ++ ")"
            (Exists  s ts x) -> "∃" ++ [s] ++ "." ++ show ts ++ "(" ++ [x] ++ ")"
            (GTEnr n r a x) -> "≥" ++ show n ++ [r] ++ "." ++ show a
            (LTEnr n r a x) -> "≤" ++ show n ++ [r] ++ "." ++ show a
            (SubSumption a b) -> show a ++ " ⊑ " ++ show b
            (Equals a b) -> show a ++ " ≡ " ++ show b
            (Distinction x y) -> [x] ++ " ≠ " ++ [y]

-- TBox and ABox are subset of [Formula], ABox doesn't have Equals predicate
data TBox = TBox [Formula] deriving Eq
data ABox = ABox [Formula] deriving Eq

instance Show TBox where
    show (TBox a) = "TBox" ++ show a

instance Show ABox where
    show (ABox a) = "ABox" ++ show a

isAnd :: Formula -> Bool
isAnd (And _ _) = True
isAnd _         = False

isOr :: Formula -> Bool
isOr (Or _ _) = True
isOr _        = False

isExists :: Formula -> Bool
isExists (Exists _ _ _) = True
isExists _ = False

isForAll :: Formula -> Bool
isForAll (ForAll _ _ _) = True
isForAll _ = False

isSubSumption :: Formula -> Bool
isSubSumption (SubSumption _ _) = True
isSubSumption _ = False

isGTEnr :: Formula -> Bool
isGTEnr (GTEnr _ _ _ _) = True
isGTEnr _ = False

isLTEnr :: Formula -> Bool
isLTEnr (LTEnr _ _ _ _) = True
isLTEnr _ = False

isEquals :: Formula -> Bool
isEquals (Equals _ _) = True
isEquals _ = False

-- simplify ¬¬ just in case
simplifyNot :: Formula -> Formula
simplifyNot f = case f of
    Not (Not a) -> a
    _ -> f

simplifyABox :: ABox -> ABox
simplifyABox abox@(ABox af) = ABox $ map simplifyNot af

-- for reduction SubSumption to Not Satisfiable
getComponents :: Formula -> (Formula, Formula)
getComponents t@(Equals a b) = (a, b)

getFormulas :: ABox -> [Formula]
getFormulas abox@(ABox af) = af

-- negate a formula recursively
negateTerm :: Formula -> Formula
negateTerm f = case f of
            Not (And a b) -> Or (negateTerm (Not a)) (negateTerm (Not b))
            Not (Or a b) -> And (negateTerm (Not a)) (negateTerm (Not b))
            Not (ForAll qt a x) -> Exists qt (negateTerm (Not a)) x
            Not (Exists qt a x) -> ForAll qt (negateTerm (Not a)) x
            Not (LTEnr n r a x) -> GTEnr (n+1) r a x        -- terminate here, no recursion
            Not (GTEnr n r a x) -> LTEnr (n-1) r a x
            _ -> f

rmSubSumption :: Formula -> Formula
rmSubSumption f = case f of
              (SubSumption a b) -> And (a) (negateTerm $ Not b)
              _ -> f

expendTerm :: (Formula, Formula) -> Formula
expendTerm pair@(a, t) = case a of
    Unary _ _ -> if a == left
                    then right
                    else a
    Not b -> Not (expendTerm (b,t))
    And b c -> And (expendTerm (b,t)) (expendTerm (c,t))
    Or b c -> Or (expendTerm (b,t)) (expendTerm (c,t))
    ForAll r b x -> ForAll r (expendTerm (b,t)) x
    Exists r b x -> Exists r (expendTerm (b,t)) x
    GTEnr n r b x -> GTEnr n r (expendTerm (b,t)) x
    LTEnr n r b x -> LTEnr n r (expendTerm (b,t)) x
    SubSumption b c -> SubSumption (expendTerm (b,t)) (expendTerm (c,t))
    otherwise -> a
    where (left, right) = getComponents t

-- expend ABox according to TBox, can only eliminate ≡, doesn't support other TBox formulas
expendABox :: TBox -> ABox -> ABox
expendABox tbox@(TBox tf) abox@(ABox af) = if length tf == 0
    then abox
    else ABox $ map expendTerm [(a,t) | a <- af, t <- tf]

genDistinct' :: (Char, Char) -> Formula
genDistinct' (x, y) = Distinction x y

genDistinct :: ABox -> ABox
genDistinct abox@(ABox af) = ABox $ af ++ (map genDistinct' (pairs $ getABoxInstances abox))

-- 1. expension, 2. eliminate subsumption 3. auto generate ≠ relation for instances
convertABox :: TBox -> ABox -> ABox
convertABox tbox abox = genDistinct $ ABox $ map rmSubSumption $ getFormulas (expendABox tbox abox)

-- assume b and c have same instances
-- you can get all instances in unary predicate
getInstances :: Formula -> [Char]
getInstances a = case a of
            Unary _ x -> x
            Relation _ x y -> [x] ++ [y]
            Not b -> getInstances b
            And b _ -> getInstances b
            Or b _ -> getInstances b
            ForAll _ b _ -> getInstances b
            Exists _ b _ -> getInstances b
            _ -> ""

getABoxInstances :: ABox -> [Char]
getABoxInstances abox@(ABox af) = rmDups $ concat $ map getInstances af

-- generate new instance
genIndividuals :: [Char] -> Int -> [Char]
genIndividuals cx n = take n (['a'..'z'] \\ cx)

updateInstances :: Formula -> Char -> Char -> Formula
updateInstances f x z = case f of
            Unary a xs -> Unary a $ map (\c -> if c == x then z else c) xs
            Not a -> Not (updateInstances a x z)
            And a b -> And (updateInstances a x z) (updateInstances b x z)
            Or a b -> Or (updateInstances a x z) (updateInstances b x z)
            ForAll qt a y -> if y == x then ForAll qt (updateInstances a x z) z else ForAll qt (updateInstances a x z) y
            Exists qt a y -> if y == x then Exists qt (updateInstances a x z) z else Exists qt (updateInstances a x z) y
            _ -> f

replaceF :: (Formula, (Char, Char)) -> Formula
replaceF (b, (x, y)) = updateInstances b x y

replaceABox :: ABox -> [Char] -> ABox
replaceABox abox@(ABox af) instances = ABox $ map replaceF $ [(f, pair) | f <- af, pair <- (pairs instances)]

-- all rules

andRule :: ABox -> Formula -> [ABox]
andRule abox@(ABox af) a = case a of
                    And c d -> [ABox $ rmDups $ (delete a af) ++ [c] ++ [d]]

orRule :: ABox -> Formula -> [ABox]
orRule abox@(ABox af) a = case a of
                    Or c d -> if not $ (elem c af)  || (elem d af)
                                then [ABox $ (delete a af) ++ [c], ABox $ (delete a af) ++ [d]]
                                else [abox, abox]

existRule :: ABox -> Formula -> [ABox]
existRule abox@(ABox af) a = case a of
                    Exists qt b x -> if length instances > 0
                                    then [ABox $ rmDups $ (delete a af) ++ map (Relation qt x) instances ++ map (updateInstances b x) instances]
                                    else [abox]
                                    where instances = filter (\y -> not $ (Relation qt x y) `elem` af && (updateInstances b x y) `elem` af) $ genIndividuals (getABoxInstances abox) 1

forallRule :: ABox -> Formula -> [ABox]
forallRule abox@(ABox af) a = case a of
                    ForAll qt b x -> if length instances > 0
                                    then [ABox $ rmDups $ (delete a af) ++ map (updateInstances b x) instances]
                                    else [abox]
                                    where instances = filter (\y -> y /= x && (((Relation qt x y) `elem` af && not ((updateInstances b x y) `elem` af)))) $ getABoxInstances abox

gteRule :: ABox -> Formula -> [ABox]
gteRule abox@(ABox af) a = case a of
            GTEnr n r b x -> if length instances < n
                        then let newinstances = genIndividuals (getABoxInstances abox) n
                                in [ABox $ af ++ map (Relation r x) newinstances ++ map (updateInstances b x) newinstances ++ map (genDistinct') (pairs newinstances)]
                        else [abox]
                        where instances = filter (\y -> y /= x && (Relation r x y) `elem` af) $ getABoxInstances abox

lteRule :: ABox -> Formula -> [ABox]
lteRule abox@(ABox af) a = case a of
    LTEnr n r b x -> if length distincts > n
                        then [replaceABox abox instances]
                        else [abox]
                        where   instances = filter (\y -> y /= x && (Relation r x y) `elem` af) $ getABoxInstances abox
                                distincts = filter (\v -> not $ elem (genDistinct' v) af) $ pairs instances

-- rule order definition
ordRule :: Formula -> Integer
ordRule f = case f of
                    (And     _ _) -> 1
                    (Or      _ _) -> 3
                    (Exists  _ _ _) -> 2
                    (ForAll  _ _ _) -> 5
                    (GTEnr _ _ _ _) -> 6
                    (LTEnr _ _ _ _) -> 4
                    _ -> 10

applyRules :: ABox -> [ABox]
applyRules abox | isAnd f = map simplifyABox $ andRule abox f
                | isOr f = map simplifyABox $ orRule abox f
                | isExists f = map simplifyABox $ existRule abox f
                | isForAll f = map simplifyABox $ forallRule abox f
                | isGTEnr f = map simplifyABox $ gteRule abox f
                | isLTEnr f = map simplifyABox $ lteRule abox f
                | otherwise = [abox]
                where   af = getFormulas abox
                        g = zip (map ordRule af) af
                        (_, f) = minimumBy (comparing fst) g

-- determine if two formulas are not conflict (A and ¬A)
nComplementaryFormula :: (Formula, Formula) -> Bool
nComplementaryFormula (f1, f2) = case f1 of
                                    Not a -> a /= f2
                                    _ -> (Not f1) /= f2

countRelations :: ABox -> Char -> Char -> Int
countRelations abox@(ABox af) r x = length $ map (\y -> (Relation r x y) `elem` af) $ getABoxInstances abox

getLTEComponents :: Formula -> (Int, Char, Formula, Char)
getLTEComponents lte@(LTEnr n r a x) = (n, r, a, x)

compareRelations :: ABox -> (Int, Char, Formula, Char) -> Bool
compareRelations abox@(ABox af) (n, r, _, x) = n < countRelations abox r x

conflictRelations :: ABox -> Bool
conflictRelations abox@(ABox af) = foldl (||) False $ map (compareRelations abox) ltecomponents
                        where   rs = filter isLTEnr af
                                ltecomponents = map getLTEComponents rs

-- abox doesn't have conflicts for number restrictions
nNewContradictionABox :: ABox -> Bool
nNewContradictionABox abox@(ABox af) = not ((foldl (||) False $ map (\x -> (Distinction x x) `elem` af) $ getABoxInstances abox)
                                    || conflictRelations abox)

-- abox is open without number restrictions
checkOpenNumABox :: ABox -> Bool
checkOpenNumABox a@(ABox xs) = foldl (&&) True $ map nComplementaryFormula [(x, l) | x <- xs, l <- xs]

checkOpenAs :: [ABox] -> Bool
checkOpenAs ax = (foldl (||) False $ map checkOpenNumABox [x | x <- ax]) && (foldl (||) False $ map nNewContradictionABox ax)

-- apply rules recursively until nothing changes
tableao' :: [ABox] -> Bool -> [ABox]
tableao' aboxes run = if run
                        then　tableao' naboxes (naboxes /= aboxes)
                        else  aboxes
                        where   naboxes = concat (map applyRules aboxes)

-- output : True for consistent ABox, False otherwise
tableao :: TBox -> ABox -> Bool
tableao tbox abox = checkOpenAs $ tableao' [convertABox tbox abox] True

main = do
    putStrLn "a0 (A consistent abox for testing, should return True) : "
    putStrLn "ABox : ∃r.A ⊓ ∃r.B ⊓ ∀r.(¬A ⊔ ¬B) "
    let a0 = ABox [And (And (Exists 'r' (Unary 'A' "a") 'a') (Exists 'r' (Unary 'B' "a") 'a')) (ForAll 'r' (Or (Not (Unary 'A' "a")) (Not (Unary 'B' "a"))) 'a')]
    putStrLn "After expension : "
    putStrLn $ show a0
    putStrLn "Final ABoxes : "
    print $ tableao' [convertABox (TBox []) a0] True
    print $ tableao (TBox []) a0

    putStrLn "\n3.1 (subsumption problem, should return False because subsumption equals to not satisfiable) : "
    putStrLn "ABox : ∀r.∀s.A ⊓ ∃r.∀s.B ⊓ ∀r.∃s.C ⊑ ∃r.∃s.(A ⊓ B ⊓ C) "
    let a1 = ABox [SubSumption (And (And (ForAll 'r' (ForAll 's' (Unary 'A' "a") 'b') 'a') (Exists 'r' (ForAll 's' (Unary 'B' "a") 'b') 'a')) (ForAll 'r' (Exists 's' (Unary 'C' "a") 'a') 'a'))
                    (Exists 'r' (Exists 's' (And (And (Unary 'A' "a") (Unary 'B' "a")) (Unary 'C' "a")) 'a') 'a')]
    putStrLn "After expension : "
    putStrLn $ show a1
    putStrLn "Final ABoxes : "
    print $ tableao' [convertABox (TBox []) a1] True
    print $ tableao (TBox []) a1

    putStrLn "\n3.2 (subsumption problem, should return False because subsumption equals to not satisfiable) : "
    putStrLn "ABox : ∀r.∀s.A ⊓ (∃r.∀s.¬A ⊔ ∀r.∃s.B) ⊑ ∀r.∃s.(A ⊓ B) ⊔ ∃r.∀s.¬B "
    let a2 = ABox [SubSumption (And (ForAll 'r' (ForAll 's' (Unary 'A' "a") 'a') 'a') (Or (Exists 'r' (ForAll 's' (Not (Unary 'A' "a")) 'a') 'a') (ForAll 'r' (Exists 's' (Unary 'B' "a") 'a') 'a')))
                    (Or (ForAll 'r' (Exists 's' (And (Unary 'A' "a") (Unary 'B' "a")) 'a') 'a') (Exists 'r' (ForAll 's' (Not (Unary 'B' "a")) 'a') 'a'))]
    putStrLn "After expension : "
    putStrLn $ show a2
    putStrLn "Final ABoxes : "
    print $ tableao' [convertABox (TBox []) a2] True
    print $ tableao (TBox []) a2

    putStrLn "\n4 (number restrictions, should return False becaue ABox is not consistent) : "
    putStrLn "TBox : P ≡ ≤2r.⊤"
    putStrLn "ABox : r(j, a), r(j, e), r(j, m), P(j)"
    let t3 = TBox [Equals (Unary 'P' "j") (LTEnr 2 'r' (Unary 'T' "j") 'j')]
    let a3 = ABox [Relation 'r' 'j' 'a', Relation 'r' 'j' 'e', Relation 'r' 'j' 'm', Unary 'P' "j"]
    putStrLn "After expension : "
    putStrLn $ show a3
    putStrLn "Final ABoxes : "
    print $ tableao' [convertABox t3 a3] True
    print $ tableao t3 a3
