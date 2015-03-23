import Test.QuickCheck

{-

HW 1: Functions: count, append, mindepth, maxdepth, tinsert.

-}

-- Let Nested a derive typeclass Eq so that testing equalify is available for quickCheck.

data Nested a = Elem a | List [Nested a]  deriving (Show, Eq)


-- The following is answer for Question 1
-- Solve the question recursively. Edge conditions can be single Elem a, List of empty list, List of single Elem a.

count :: Nested a -> Int       --This count function is designed especially for list of type: Nested a

count (Elem _) = 1                -- Edge condition, for Elem a
count (List []) = 0               -- Edge condition, for List []
count (List [Elem _]) = 1         -- Edge condition, for List [Elem _]
count (List (x:xs)) = count x + count (List xs)         --Recursively count the first (Nested a) element and count of rest elements in new List, sum two counts together



-- The following is answer for Question 2


append :: (Nested a) -> (Nested a) -> Either String (Nested a)

append (Elem _) _ = Left $ "Ooops, I can only append two nested lists. Correct your inputs."       -- String output to show error message
append _ (Elem _) = Left $ "Ooops, I can only append two nested lists. Correct your inputs."

append (List x1) (List x2) = Right $ List (concat [x1,x2])                 -- use builtin concat :: [[a]] -> [a] to append two nested lists





-- The following is answer for Question 3

data Tree a = Empty | Branch a (Tree a) (Tree a)
                  deriving (Show, Eq)


mindepth :: Tree a -> Int


-- mindepth has 3 edge conditions, else perform recursively (down to Empty)
-- Built-in function min :: (Ord a) => a -> a -> a was used to compare mindepths of left and right subtrees.
mindepth (Empty) = 0
mindepth (Branch _ (Empty) (_)) = 1
mindepth (Branch _ (_) (Empty)) = 1
mindepth (Branch _ left right) = (min (mindepth left) (mindepth right)) + 1 




maxdepth :: Tree a -> Int

-- maxdepth has an edge condition of Empty, else perform recursively (down to empty tree)
-- Built-in function max :: (Ord a) => a -> a -> a was used to compare maxdepths of left and right subtrees.
maxdepth (Empty) = 0
maxdepth (Branch _ left right) = (max (maxdepth left) (maxdepth right)) + 1




-- The following is answer for Question 4


-- A helper function singleton to insert a new node into Empty
singleton :: a -> Tree a
singleton x = Branch x (Empty) (Empty)


-- tinsert has edge condition of inserting into empty tree, then recursively find the appropriate spot to insert.
-- Arguments order: argument of (Tree a) first, then the element to be inserted.
-- use "@" to conveniently refers to whole tree. If element already exists, simply returns the original tree.
tinsert :: (Ord a) => Tree a -> a -> Tree a

tinsert Empty x = singleton x
tinsert tree@(Branch a left right) x
	| x == a  = tree
	| x < a	  = Branch a (tinsert left x) right
	| x > a   = Branch a left (tinsert right x)



{-
The followings are test cases.

testCount: test function count 
testAppend: test function append
testMindepth: test function mindepth
testMaxdepth: test function maxdepth
testInsert: test function tinsert

Each function is tested by two case.
-}

-- Test count function

testCount = 
	let test = List [Elem 1, Elem 2, List [Elem 3, Elem 4], List [Elem 5], Elem 6]
	    test2 = List [List [List [Elem 1, Elem 2], List [Elem 3]], Elem 4, Elem 5, List [Elem 6, Elem 7, Elem 8, Elem 9]]
	in
	do
		quickCheck (count test == 6)
		quickCheck (count test2 == 9)


-- Test append function

testAppend = 
	let test = (Elem 1)
	    test2 = List [Elem 1, Elem 2, List [Elem 3, Elem 4], List [Elem 5], Elem 6]
	    test3 = List [List [List [Elem 1, Elem 2], List [Elem 3]], Elem 4, List [Elem 5, Elem 6]]
--	    r :: Either String (Nested Int)                                                  -- Anticipated r type, not used in code, just for understanding
	    r = Left $ "Ooops, I can only append two nested lists. Correct your inputs."                     -- The expected result to show error message 
--	    r2 :: Either String (Nested Int)
	    r2 = Right $ List [Elem 1, Elem 2, List [Elem 3, Elem 4], List [Elem 5], Elem 6, List [List [Elem 1, Elem 2], List [Elem 3]], Elem 4, List[Elem 5, Elem 6]] -- Expected result of appending
	in
	do
		quickCheck (append test test2 == r)
		quickCheck (append test2 test3 == r2)



-- Define two trees used as mindepth, maxdepth, tinsert function test case
tree1 = Branch 10 (Branch 5 (Branch 3 Empty Empty) Empty) Empty
tree2 = Branch 10 (Branch 5 (Branch 3 Empty (Branch 4 Empty Empty)) Empty) (Branch 11 Empty Empty)


-- Test mindepth function

testMindepth = 
	let test = tree1
	    test2 = tree2
	in
	do
		quickCheck (mindepth test == 1)
		quickCheck (mindepth test2 == 2)


-- Test maxdepth function

testMaxdepth =
	let test = tree1
	    test2 = tree2
	in
	do
		quickCheck (maxdepth test == 3)
		quickCheck (maxdepth test2 == 4)


-- Test tinsert function
-- My tinsert function takes a parameter of (Tree a) and a parameter of type a in order. So calling (tinsert test 3) can test it, as below.

testInsert =
	let test = tree1
	    test2 = tree2
      	    result = Branch 10 (Branch 5 (Branch 3 Empty (Branch 4 Empty Empty)) (Branch 6 Empty Empty)) (Branch 11 Empty Empty)        --The expected new tree after insert 6 into test2
	in
        do
            quickCheck (tinsert test 3 == test)                             -- should return the original tree
            quickCheck (tinsert test2 6 == result)

main = 
	do
		putStrLn "Now testing function count..."
		testCount
		putStrLn "Now testing function append..."
		testAppend
		putStrLn "Now testing function mindepth..."
		testMindepth
		putStrLn "Now testing function maxdepth..."
		testMaxdepth
		putStrLn "Now testing function tinsert..."
		testInsert

