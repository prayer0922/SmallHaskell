import Test.QuickCheck

{-

You can run this file by: runhaskell hw2p5.hs

-}
-- Abstract syntax of arithmetic expressions
data Aexp = IntExp Int
    | LocExp String
    | PlusExp Aexp Aexp
    | MinusExp Aexp Aexp
    | TimesExp Aexp Aexp

-- Abstract syntax of boolean expressions
data Bexp = TrueExp
    | FalseExp
    | EqualsExp Aexp Aexp
    | LessExp Aexp Aexp
    | NotExp Bexp
    | AndExp Bexp Bexp
    | OrExp Bexp Bexp

-- Abstract syntax of commands
data Comm = Pass
    | Seq Comm Comm
    | IfThenElse Bexp Comm Comm
    | While Bexp Comm
    | RepeatUntil Bexp Comm       -- Added to handle repeat c until e construct
    | Set String Aexp

-- State
data State = Empty
    | Assign String Int State
    deriving (Eq, Show)

-- Find a variable binding, return 0 by default
find :: State -> String -> Int
find Empty _ = 0
find (Assign x0 v0 s0) x =
    if x == x0 then v0 else find s0 x

-- Update state with assignment
update :: State -> String -> Int -> State
update s x v = Assign x v s

-- Evaluate an arithmetic expression
evalA :: Aexp -> State -> Int
evalA (IntExp n) _env = n
evalA (LocExp v) env = find env v
evalA (PlusExp e1 e2) env = (evalA e1 env) + (evalA e2 env)
evalA (MinusExp e1 e2) env = (evalA e1 env) - (evalA e2 env)
evalA (TimesExp e1 e2) env = (evalA e1 env) * (evalA e2 env)

-- Evaluate a boolean expression
evalB :: Bexp -> State -> Bool
evalB TrueExp _env = True
evalB FalseExp _env = False
evalB (EqualsExp e1 e2) env = (evalA e1 env) == (evalA e2 env)
evalB (LessExp e1 e2) env = (evalA e1 env) < (evalA e2 env)
evalB (NotExp b) env = not (evalB b env)
evalB (AndExp b1 b2) env = (evalB b1 env) && (evalB b2 env)
evalB (OrExp b1 b2) env = (evalB b1 env) || (evalB b2 env)

-- Evaluate a command
evalC :: Comm -> State -> State
evalC Pass env = env
evalC (Seq c1 c2) env = 
    let env' = evalC c1 env in
    evalC c2 env'
evalC (IfThenElse b c1 c2) env =
    if bv then evalC c1 env else evalC c2 env
    where bv = evalB b env
evalC (While b c) env =
    if bv then evalC (Seq c (While b c)) env else env
    where bv = evalB b env


-- Code added to handle repeat c until e 
evalC (RepeatUntil b c) env =
    if bv then env' else evalC (RepeatUntil b c) env'
    where env' = evalC c env
          bv = evalB b env'

evalC (Set x e) env =
    update env x (evalA e env)


-- Test cases 

testFindUpdate = 
    let state1 = update (Assign "y" 6 Empty) "x" 5         -- update a state with assignment to var1
    in
    do
        quickCheck (find Empty "x" == 0)                  -- test find in Empty state
        quickCheck (find state1 "x" == 5)                 -- test find in updated state
	    

testEvalA = 
    let state2 = Assign "x" 12 Empty 
    in
    do
        quickCheck (evalA (PlusExp (LocExp "x") (IntExp 1)) state2 == 13)         -- in state2, x := 12, so PlusExp evaluates to 13
        quickCheck (evalA (TimesExp (LocExp "x") (IntExp 12)) Empty == 0)         -- in Empty, x assigned to zero, so TimesExp evaluates to 0


testEvalB = 
    let b1 = LessExp (IntExp 4) (IntExp 2)
    in
    do
       quickCheck (evalB (EqualsExp (LocExp "x") (IntExp 0)) Empty == True)        -- in Empty, x assigned to zero
       quickCheck (evalB (OrExp TrueExp b1) Empty == True)




-- Test cases for evalC including Repeat Until

testEvalRepeat =
    let v1 = Set "x" (IntExp 1)                -- v1 as assignment x := 1
        b1 = NotExp $ LessExp (LocExp "x") (IntExp 10)         -- if x ≥ 10
        v2 = Set "x" (PlusExp (LocExp "x") (IntExp 2))         -- x := x + 2
        b2 = NotExp $ LessExp (PlusExp (LocExp "x") (LocExp "y")) (IntExp 24)         -- if x + y ≥ 24
        program1 = Seq v1 (RepeatUntil b1 v2)        -- sequence of v1; repeat v2 until b1
        program2 = Seq v1 (RepeatUntil b2 v2)        -- sequence of v1; repeat v2 until b2
        program3 = IfThenElse b1 (Set "x" (IntExp 1)) (Set "x" (IntExp 0))             -- set x to 1 or 0 according to b1
        result1 = Assign "x" 11 (Assign "x" 9 (Assign "x" 7 (Assign "x" 5 (Assign "x" 3 (Assign "x" 1 Empty)))))
        result2 = Assign "x" 13 (Assign "x" 11 (Assign "x" 9 (Assign "x" 7 (Assign "x" 5 (Assign "x" 3 (Assign "x" 1 (Assign "y" 11 Empty)))))))
        result3 = Assign "x" 1 (Assign "x" 11 (Assign "x" 9 (Assign "x" 7 (Assign "x" 5 (Assign "x" 3 (Assign "x" 1 Empty))))))
    in
    do
        quickCheck (evalC program1 Empty == result1)
        quickCheck (evalC program2 (Assign "y" 11 Empty) == result2)
        quickCheck (evalC program3 result1 == result3)
        quickCheck (evalC Pass result3 == result3)


-- A test program
main :: IO ()
main =
    let i1 = Set "x" (IntExp 1)
        i2 = Set "y" (IntExp 10)
        b = LessExp (LocExp "x") (IntExp 10)
        i3 = Set "x" (PlusExp (LocExp "x") (IntExp 1))
        prg = Seq i1 (Seq i2 (While b i3)) in
    do
        print $ evalC (Set "x" (IntExp 5)) Empty
        print $ evalC prg Empty
        putStrLn "Testing find and update..."
        testFindUpdate
        putStrLn "Testing evalA..."
        testEvalA
        putStrLn "Testing evalB..."
        testEvalB
        putStrLn "Testing evalC and Repeat c Until e..."
        testEvalRepeat
