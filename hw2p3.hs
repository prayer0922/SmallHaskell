import Control.Applicative
import Data.Either
import Test.QuickCheck

{-
You can run this file by: runhaskell hw2p3.hs
-}


-- new type ARITH. There is no way to directly refer to OVERFLOW in ARITH.
data ARITH = IntExp Int
    | PlusExp ARITH ARITH
    | ProdExp ARITH ARITH
    deriving (Show, Eq)


-- checkRange checkes whether the integer literal is within the range.
checkRange :: Int -> Either String Int
checkRange n 
    | (n >= 0 && n <= 255) = Right n               -- If in the range, return Right n
    | otherwise = Left "OVERFLOW"                  -- Otherwise, Left "OVERFLOW" denotes overflows


-- transform erases the type constructor and add code reusability for +, * cases
transform :: (Int -> Int -> Int) -> ARITH -> Either String Int
transform f (PlusExp e1 e2) = evalHelper f e1 e2
transform f (ProdExp e1 e2) = evalHelper f e1 e2
transform _ _ = Left "Not to be run here"          -- Just for exhaustive pattern matching


-- evalHelper takes two ARITH, apply function f to them, using that Either a is an instance of Applicative and Monad
evalHelper :: (Int -> Int -> Int) -> ARITH -> ARITH -> Either String Int
evalHelper f e1 e2
    | (isLeft n1 || isLeft n2) = Left "OVERFLOW"
    | isLeft (n >>= \x -> (checkRange x)) = Left "OVERFLOW"       -- instance of Monad, (>>=) helps transformation between normal and monadic values
    | otherwise = n
    where n1 = eval e1
          n2 = eval e2
          n = pure f <*> n1 <*> n2                 -- instance of Applicative, pure (+) <*> Right 5 <*> Right 9 will return Right 14, etc.


{-
Function eval calls helper function and returns either Integer literals or "OVERFLOW" (in type of Either String Int)
For PlusExp ProdExp operations, if at least one ARITH is OVERFLOW, the result is OVERFLOW
If the evaluation overflows, the result is OVERFLOW, otherwise an Integer
-}

eval :: ARITH -> Either String Int
eval (IntExp n)= checkRange n
eval (PlusExp e1 e2) = transform (+) (PlusExp e1 e2)      
eval (ProdExp e1 e2) = transform (*) (ProdExp e1 e2)



-- Test cases
testEval = 
    let x2 = IntExp 4
        x3 = IntExp 7
        x4 = IntExp 250
        x5 = IntExp 500
    in
    do
        quickCheck (eval x3 == Right 7)
	quickCheck (eval x5 == Left "OVERFLOW")
        quickCheck (eval (PlusExp x2 x3) == Right 11)
        quickCheck (eval (PlusExp x3 x4) == Left "OVERFLOW")
        quickCheck (eval (PlusExp x5 x3) == Left "OVERFLOW")
        quickCheck (eval (ProdExp x2 x3) == Right 28)
        quickCheck (eval (ProdExp x2 x4) == Left "OVERFLOW")


main = do
	testEval


