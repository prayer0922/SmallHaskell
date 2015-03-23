{-
As a preparation for implementation, the following is definitions for problem 1 to 3.

1. xor = λb.λc.b (c fls tru) c;  

Provement of xor fls tru ⇓ tru:

                              _________
 xor ⇓ λb.λc.b (c fls tru) c  fls ⇓ fls   λc.b (c fls tru) { b -> fls} ⇓ λc.fls (c fls tru)
 _________________________________________________________________________________________     _________
 (xor fls) ⇓ λc.fls (c fls tru) c                                                              tru ⇓ tru    fls (c fls tru) c {c -> tru} ⇓ fls (tru fls tru) tru 
 _______________________________________________________________________________________________________________________________________________________________
 (xor fls) tru ⇓ fls (tru fls tru) tru

Then, to evaluate fls (tru fls tru) tru, we first eval (tru fls tru):

               _________ 
 tru ⇓ λt.λf.t fls ⇓ fls  λf.t {t -> fls} ⇓ λf.fls
 _________________________________________________     _________  
 tru fls ⇓ λf.fls                                      tru ⇓ tru  fls {f -> tru}  ⇓ fls 
 _______________________________________________________________________________________
 (tru fls) tru ⇓ fls


Finally, under same process, fls fls tru ⇓ tru, the statement holds.

               _________ 
 fls ⇓ λt.λf.f fls ⇓ fls  λf.f {t -> fls} ⇓ λf.f
 _________________________________________________     _________  
 fls fls ⇓ λf.f                                        tru ⇓ tru  f {f -> tru}  ⇓ tru 
 _______________________________________________________________________________________
 (fls fls) tru ⇓ tru


2. nonZero = λm.m (λx.tru) fls;

3. nil = λhh.λtt.tt;
   cons = λh.λt.λhh.λtt.hh h (t hh tt);
   isNil = λl.l (λh.λt.fls) tru;
   head = λl.l (λh.λt.h) fls;

   ss' = λx.λp.pair (snd p) (cons x (snd p));
   zz' = pair nil nil;
   tail = λl.fst (l ss' zz');
-}


import Test.QuickCheck
import Data.List

----- Problem 4 ----- 
type Variable = String

data Term = TmVar Variable
    | TmAbs Variable Term
    | TmApp Term Term

infixl 8 `TmApp`
infixr 9 `TmAbs`


-- make Term instance of Show
-- Parentheses explicitly indicate associations for abstractions and applications.
instance Show Term where 
   show (TmVar x) = x
   show (TmApp t1 t2) = "(" ++ (show t1) ++ " " ++ (show t2) ++ ")"
   show (TmAbs x t) = "(\\" ++ x ++ "." ++ (show t) ++ ")"

-- Overwrite "==" to check for alpha-equivalence (equal up to renaming)
-- But not for checking equivalence under Normal Form transformation.
instance Eq Term where
   (TmVar x) == (TmVar y) = x == y
   (TmAbs varx t1) == (TmAbs vary t2) 
        | varx == vary = t1 == t2
        | otherwise =
                let swapName (TmVar var) varx vary           -- swap varx vary to rename
                             | var == varx = (TmVar vary)
                             | var == vary = (TmVar varx)
                             | otherwise = (TmVar var)
                    swapName (TmAbs var t) varx vary
                             | var == varx = (TmAbs vary (swapName t varx vary))
                             | var == vary  = (TmAbs varx (swapName t varx vary))
                             | otherwise = (TmAbs var (swapName t varx vary))
                    swapName (TmApp t1 t2) varx vary = TmApp (swapName t1 varx vary) (swapName t2 varx vary)
                in (swapName t1 varx vary) == t2 
   (TmApp t1 t2) == (TmApp t3 t4) = ((t1 == t3) && (t2 == t4))
   _ == _ = False




-- isValue determines if a term is a value (abstratcion) or not.
isValue :: Term -> Bool
isValue (TmAbs _ _) = True
isValue _ = False


-- freeList helper function generate list of free variables
freeList :: Term -> [Variable]
freeList (TmVar x) = [x]
freeList (TmAbs x t) = filter (/= x) (freeList t)
freeList (TmApp t1 t2) = (freeList t1) `union` (freeList t2)


-- allVars helper function returns a list of all variables in term
allVars :: Term -> [Variable]
allVars (TmVar x) = [x]
allVars (TmAbs x t) = x:(allVars t)       -- duplicates here do not matter
allVars (TmApp t1 t2) = (allVars t1) `union` (allVars t2)





-- subst does substitution recursively, alpha renaming if necessary
subst :: Variable -> Term -> Term -> Term
subst x s b = sub vs0 b where          -- {x -> s}b
    sub _ e@(TmVar v)
        | v == x = s
        | otherwise = e
    sub vs e@(TmAbs v e')
        | v == x = e
        | v `elem` fvs = TmAbs v' (sub (v':vs) e'')     -- alpha renaming, get new name v' from infinite list(except invalid names)
        | otherwise = TmAbs v (sub vs e') where
        v' = newId vs        -- get a new valid name
        e'' = subst v (TmVar v') e'
    sub vs (TmApp f a) = sub vs f `TmApp` sub vs a
    fvs = freeList s
    vs0 = fvs `union` allVars b     -- vs0 are invalid variable names in FV(s) and all vars in b


-- get a new name from the infinite variable list  
newId :: [Variable] -> Variable
newId vs = head (names \\ vs)         -- vs are invalid variable names


-- get an infinite variable name list
names :: [Variable]
names = [ [i] | i <- ['a'..'z']] ++ [i : show j | j <- [1..], i <- ['a'..'z'] ]




-- eval evaluates a term
eval :: Term -> Either String Term
eval (TmApp (TmAbs varx t12) t2@(TmAbs _ _)) = eval (subst varx t2 t12)    -- Beta Reduction
eval (TmApp t1@(TmAbs _ _) t2) = let t2' = eval t2 in t2' >>= \x -> eval (TmApp t1 x)     -- Application 2, call-by-value
eval (TmApp t1 t2) = let t1' = eval t1 in t1' >>= \x -> eval (TmApp x t2)  -- Application 1, call-by-value
eval t
    | isValue t = return t           -- Already an abstraction
    | otherwise = Left "ERROR INPUT!"   -- A term variable is not valid for evaluation




-- Test cases --
testLamda =
-- common terms used in test
    let tru = TmAbs "t" $ TmAbs "f" (TmVar "t")
        fls = TmAbs "t" $ TmAbs "f" (TmVar "f")
        and = TmAbs "b" $ TmAbs "c" $ (TmVar "b") `TmApp` (TmVar "c") `TmApp` fls 
        id = TmAbs "x" $ TmVar "x"
        pair = TmAbs "f" $ TmAbs "s" $ TmAbs "b" $ (TmVar "b") `TmApp` (TmVar "f") `TmApp` (TmVar "s")     
        fst = TmAbs "p" $ (TmVar "p") `TmApp` tru
        snd =  TmAbs "p" $ (TmVar "p") `TmApp` fls
        zero =  TmAbs "s" $ TmAbs "z" $ TmVar "z"
        one = TmAbs "s" $ TmAbs "z" $ (TmVar "s") `TmApp` (TmVar "z")
        zz = (TmApp pair zero) `TmApp` zero
        plus = TmAbs "m" $ TmAbs "n" $ TmAbs "s" $ TmAbs "z" $ (TmVar "m") `TmApp` (TmVar "s") `TmApp` ((TmVar "n") `TmApp` (TmVar "s") `TmApp` (TmVar "z")) 
        ss = TmAbs "p" $ pair `TmApp` (snd `TmApp` (TmVar "p")) `TmApp` (plus `TmApp` one `TmApp` (snd `TmApp` (TmVar "p")))
        pred = TmAbs "m" $ fst `TmApp` ((TmVar "m") `TmApp` ss `TmApp` zz)
-- Solutions for Problem 1,2,3
        xor = TmAbs "b" $ TmAbs "c" $ (TmVar "b") `TmApp` ((TmVar "c") `TmApp` fls `TmApp` tru) `TmApp` (TmVar "c")                  -- xor = λb.λc.b (c fls tru) c;
        nonZero = TmAbs "m" $ (TmVar "m") `TmApp` (TmAbs "x" tru) `TmApp` fls    -- nonZero = λm.m (λx.tru) fls;
        nil = TmAbs "hh" $ TmAbs "tt" $ TmVar "tt"                                     -- nil = λhh.λtt.tt;
-- cons = λh.λt.λhh.λtt.hh h (t hh tt);
        cons = TmAbs "h" $ TmAbs "t" $ TmAbs "hh" $ TmAbs "tt" $ (TmVar "hh") `TmApp` (TmVar "h") `TmApp` ((TmVar "t") `TmApp` (TmVar "hh") `TmApp` (TmVar "tt")) 
        isNil = TmAbs "l" $ (TmVar "l") `TmApp` (TmAbs "h" $ TmAbs "t" $ fls) `TmApp` tru                      --  isNil = λl.l (λh.λt.fls) tru;
        head = TmAbs "l" $ (TmVar "l") `TmApp` (TmAbs "h" $ TmAbs "t" $ TmVar "h") `TmApp` fls                        --  head = λl.l (λh.λt.h) fls;
--ss'=λx.λy.pair (snd y) (cons x (snd y))
        ss' = TmAbs "x" $ TmAbs "y" $ pair `TmApp` (snd `TmApp` (TmVar "y")) `TmApp` (cons `TmApp` (TmVar "x") `TmApp` (snd `TmApp` (TmVar "y"))) 
        zz' = pair `TmApp` nil `TmApp` nil      --  zz' = pair nil nil;
        tail = TmAbs "l" $ fst `TmApp` ((TmVar "l") `TmApp` ss' `TmApp` zz')                          -- tail = λl.fst (l ss' zz');  (Similar to pred)
        list1 = cons `TmApp` one `TmApp` nil                                  -- prepend one to empty list (nil)
        list2 = cons `TmApp` zero `TmApp` list1                               -- prepend zero to list above
    in
    do
        putStrLn "\nNow testing lambda calculus"
        quickCheck (eval (TmVar "x") == Left "ERROR INPUT!")                  
        quickCheck (eval (id `TmApp` tru) == Right tru)                               
        quickCheck (eval (and `TmApp` tru `TmApp` tru) == Right tru)                  -- and tru tru ⇓ tru
        quickCheck (eval zero == eval (pred `TmApp` one))                             -- pred one ⇓ zero
        putStrLn "Test cases for subst and isValue"
        quickCheck ((subst "x" (TmAbs "z" $ (TmVar "z") `TmApp` (TmVar "w")) (TmAbs "y" $ TmVar "x")) 
                        == (TmAbs "y" $ TmAbs "z" $ (TmVar "z") `TmApp` (TmVar "w")))       -- substitution {x -> (λz.z w)} (λy.x) = (λy.λz.z w) 
        quickCheck ((subst "x" ((TmVar "y") `TmApp` (TmVar "z")) (TmAbs "y" $ (TmVar "x") `TmApp` (TmVar "y"))) 
                              == (TmAbs "w" $ (TmVar "y") `TmApp` (TmVar "z") `TmApp` (TmVar "w")))   -- substitution {x -> y z} (λy. x y) = (λw. y z w)
        quickCheck (isValue tru == True)
        quickCheck (isValue ((TmVar "x") `TmApp` (TmVar "y")) == False)
        putStrLn "Test cases for XOR"
        quickCheck (eval (xor `TmApp` tru `TmApp` tru) == Right fls)                 -- 2 test cases for XOR
        quickCheck (eval (xor `TmApp` fls `TmApp` tru) == Right tru)                 -- xor fls tru ⇓ tru
        putStrLn "Test cases for nonZero"
        quickCheck (eval (nonZero `TmApp` zero) == Right fls)                       
        quickCheck (eval (nonZero `TmApp` one) == Right tru)
        quickCheck (eval (nonZero `TmApp` (pred `TmApp` one)) == Right fls)           -- (nonZero (pred one)) evaluates to Right fls
        putStrLn "Test cases for isNil, nil and cons"
        quickCheck (eval (isNil `TmApp` nil) == Right tru)
        quickCheck (eval (isNil `TmApp` list1) == Right fls)    
        putStrLn "Test cases for head and tail"
        quickCheck (eval (head `TmApp` list2) == Right zero)
        quickCheck (eval (isNil `TmApp` (head `TmApp` nil)) == Right tru)                 -- head of nil is nil
        quickCheck ((eval (tail `TmApp` list2)) == (eval list1))                        -- list2: cons zero list1, so tail is list1
        quickCheck (eval (tail `TmApp` list1) == Right nil)




----- Problem 5 -----
data DeTerm = DeVar Int         -- Variable referenced by Int instead of String
    | DeAbs DeTerm              -- No need to reserve variable because no restoreName funtion from unnamed to named Term
    | DeApp DeTerm DeTerm
    deriving (Eq)

infixl 8 `DeApp`
infixr 9 `DeAbs`

instance Show DeTerm where
    show (DeVar x) = show x
    show (DeApp t1 t2) = "(" ++ (show t1) ++ " " ++(show t2) ++ ")"
    show (DeAbs t) = "(\\" ++ "." ++ (show t) ++ ")"


type NameContext = [Variable]

context :: Term -> NameContext
context = freeList            -- get free variable list

removeNames :: NameContext -> Term -> DeTerm
removeNames ctx (TmVar x) = let idMaybe = elemIndex x ctx in maybe (DeVar (-7)) (DeVar) idMaybe     -- idMaybe :: Maybe Int, if Nothing, return -7, or return index.
removeNames ctx (TmAbs x t) = DeAbs (removeNames (x:ctx) t)
removeNames ctx (TmApp t1 t2) = DeApp (removeNames ctx t1) (removeNames ctx t2)

shift :: Int -> DeTerm -> DeTerm                -- shift rules
shift d = goWith 0 where      -- add cutoff (0)
              goWith cutoff t = case t of
                     DeVar k -> DeVar $ if k < cutoff then k else k + d
                     DeAbs t1 -> DeAbs $ goWith (cutoff + 1) t1
                     DeApp t1 t2 -> DeApp (goWith cutoff t1) (goWith cutoff t2)


substitute :: Int -> DeTerm -> DeTerm -> DeTerm           -- substitution rules
substitute j s t = case t of
                       DeVar k -> if j == k then s else (DeVar k)
                       DeAbs t -> DeAbs (substitute (j+1) (shift 1 s) t)
                       DeApp t1 t2 -> DeApp (substitute j s t1) (substitute j s t2)


eBeta :: DeTerm -> DeTerm -> DeTerm
eBeta v2 t1 = shift (-1) $ substitute 0 (shift 1 v2) t1        -- beta reduction rule

isValue2 :: DeTerm -> Bool           -- decide if it is an abstraction (value)
isValue2 (DeAbs _) = True
isValue2 _ = False

eval2 :: DeTerm -> Either String DeTerm
eval2 t = case t of
              DeApp (DeAbs t1) v2
                   | isValue2 v2 -> eval2 $ eBeta v2 t1            -- beta-reduction
              DeApp v1 t2
                   | isValue2 v1 -> let t2' = eval2 t2 in t2' >>= (\x -> eval2 (DeApp v1 x))  -- application rule
              DeApp t1 t2 -> let t1' = eval2 t1 in t1' >>= (\x -> eval2 (DeApp x t2))          -- application rule
              DeAbs t -> return (DeAbs t)       -- already a value
              _ ->  Left "ERROR INPUT!"         -- No rules can be applied



--- Test cases ---
testNameless =
--  named terms used in test
    let tru = TmAbs "t" $ TmAbs "f" (TmVar "t")
        fls = TmAbs "t" $ TmAbs "f" (TmVar "f")
        and = TmAbs "b" $ TmAbs "c" $ (TmVar "b") `TmApp` (TmVar "c") `TmApp` fls 
        id = TmAbs "x" $ TmVar "x"
        pair = TmAbs "f" $ TmAbs "s" $ TmAbs "b" $ (TmVar "b") `TmApp` (TmVar "f") `TmApp` (TmVar "s")     
        fst = TmAbs "p" $ (TmVar "p") `TmApp` tru
        snd =  TmAbs "p" $ (TmVar "p") `TmApp` fls
        zero =  TmAbs "s" $ TmAbs "z" $ TmVar "z"
        one = TmAbs "s" $ TmAbs "z" $ (TmVar "s") `TmApp` (TmVar "z")
        zz = (TmApp pair zero) `TmApp` zero
        plus = TmAbs "m" $ TmAbs "n" $ TmAbs "s" $ TmAbs "z" $ (TmVar "m") `TmApp` (TmVar "s") `TmApp` ((TmVar "n") `TmApp` (TmVar "s") `TmApp` (TmVar "z")) 
        ss = TmAbs "p" $ pair `TmApp` (snd `TmApp` (TmVar "p")) `TmApp` (plus `TmApp` one `TmApp` (snd `TmApp` (TmVar "p")))
        pred = TmAbs "m" $ fst `TmApp` ((TmVar "m") `TmApp` ss `TmApp` zz)
-- Solutions for Problem 1,2,3
        xor = TmAbs "b" $ TmAbs "c" $ (TmVar "b") `TmApp` ((TmVar "c") `TmApp` fls `TmApp` tru) `TmApp` (TmVar "c")                  -- xor = λb.λc.b (c fls tru) c;
        nonZero = TmAbs "m" $ (TmVar "m") `TmApp` (TmAbs "x" tru) `TmApp` fls    -- nonZero = λm.m (λx.tru) fls;
        nil = TmAbs "hh" $ TmAbs "tt" $ TmVar "tt"                                     -- nil = λhh.λtt.tt;
-- cons = λh.λt.λhh.λtt.hh h (t hh tt);
        cons = TmAbs "h" $ TmAbs "t" $ TmAbs "hh" $ TmAbs "tt" $ (TmVar "hh") `TmApp` (TmVar "h") `TmApp` ((TmVar "t") `TmApp` (TmVar "hh") `TmApp` (TmVar "tt")) 
        isNil = TmAbs "l" $ (TmVar "l") `TmApp` (TmAbs "h" $ TmAbs "t" $ fls) `TmApp` tru                      --  isNil = λl.l (λh.λt.fls) tru;
        head = TmAbs "l" $ (TmVar "l") `TmApp` (TmAbs "h" $ TmAbs "t" $ TmVar "h") `TmApp` fls                        --  head = λl.l (λh.λt.h) fls;
-- ss'=λx.λy.pair (snd y) (cons x (snd y))
        ss' = TmAbs "x" $ TmAbs "y" $ pair `TmApp` (snd `TmApp` (TmVar "y")) `TmApp` (cons `TmApp` (TmVar "x") `TmApp` (snd `TmApp` (TmVar "y"))) 
        zz' = pair `TmApp` nil `TmApp` nil      --  zz' = pair nil nil;
        tail = TmAbs "l" $ fst `TmApp` ((TmVar "l") `TmApp` ss' `TmApp` zz')                          -- tail = λl.fst (l ss' zz');  (Similar to pred)
        list1 = cons `TmApp` one `TmApp` nil                                  -- prepend one to empty list (nil)
        list2 = cons `TmApp` zero `TmApp` list1                               -- prepend zero to list above
        deTru = DeAbs $ DeAbs $ DeVar 1
        deFls = DeAbs $ DeAbs $ DeVar 0
        deAnd = DeAbs $ DeAbs $ (DeVar 1) `DeApp` (DeVar 0) `DeApp` (DeAbs $ DeAbs $ DeVar 0)
        dePlus = DeAbs $ DeAbs $ DeAbs $ DeAbs $ (DeVar 3) `DeApp` (DeVar 1) `DeApp` ((DeVar 2) `DeApp` (DeVar 1) `DeApp` (DeVar 0))
-- Converting to Nameless representations.
        deNonZero = removeNames (context nonZero) nonZero
        deOne = removeNames (context one) one
        deNil = removeNames (context nil) nil
        deIsNil = removeNames (context isNil) isNil
        deHead = removeNames (context head) head
        deTail = removeNames (context tail) tail
        deList1 = removeNames (context list1) list1
        deList2 = removeNames (context list2) list2
    in
    do
        putStrLn "\nNow testing nameless representations"
        putStrLn "Test removeNames, substitute and shift ..."
        quickCheck((removeNames (context tru) tru) == deTru)
        quickCheck((removeNames (context and) and) == deAnd)
        quickCheck((removeNames (context plus) plus) == dePlus)
        quickCheck((substitute 0 ((DeVar 1) `DeApp` (DeVar 2)) (DeAbs $ (DeVar 0) `DeApp` (DeVar 1))) 
                           == (DeAbs $ (DeVar 0) `DeApp` ((DeVar 2) `DeApp` (DeVar 3))))         -- (λ.0 1) {0 -> 1 2} -> λ.0 (2 3) 
        quickCheck((substitute 0 (DeVar 1) ((DeVar 0) `DeApp` (DeAbs $ DeAbs $ (DeVar 2)))) 
                           == ((DeVar 1) `DeApp` (DeAbs $ DeAbs $ (DeVar 3))))                   -- (0 (λ.λ.2)) {0 -> 1} -> (1 λ.λ.3)
        quickCheck((shift 2 (DeAbs $ DeAbs $ (DeVar 1) `DeApp` ((DeVar 0) `DeApp` (DeVar 2))))
                           == (DeAbs $ DeAbs $ (DeVar 1) `DeApp` ((DeVar 0) `DeApp` (DeVar 4))))    -- shift 2 (λ.λ.1 (0 2)) -> λ.λ.1 (0 4)
        putStrLn "Test unnamed id, XOR ..."
        quickCheck((eval2 ((removeNames (context id) id) `DeApp` deTru)) == Right deTru)
        quickCheck((eval2 ((removeNames (context xor) xor) `DeApp` deTru `DeApp` deTru)) == Right deFls)
        quickCheck((eval2 ((removeNames (context xor) xor) `DeApp` deFls `DeApp` deTru)) == Right deTru)    -- xor fls tru ⇓ tru, other test cases are same with problem 4
        putStrLn "Test unnamed nonZero, isNil, nil and cons ..."
        quickCheck((eval2 (deNonZero `DeApp` deOne)) == Right deTru)
        quickCheck((eval2 (deNonZero `DeApp` ((removeNames (context pred) pred) `DeApp` deOne))) == Right deFls)
        quickCheck((eval2 (deIsNil `DeApp` deNil)) == Right deTru)  
        quickCheck((eval2 (deIsNil `DeApp` deList2)) == Right deFls)     
        putStrLn "Test unnamed head and tail ..."
        quickCheck((eval2 (deHead `DeApp` deList1)) == Right deOne)
        quickCheck((eval2 (deIsNil `DeApp` (deHead `DeApp` deNil))) == Right deTru) 
        quickCheck((eval2 (deTail `DeApp` deList2)) == (eval2 deList1))
        quickCheck((eval2 (deTail `DeApp` deList1)) == Right deNil)


main = do
        testLamda
        testNameless


