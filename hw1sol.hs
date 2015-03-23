import Test.QuickCheck



-- Heterogeneous Lists ------------------------

data Nested a = Elem a
              | List [Nested a]
              deriving (Show, Eq)

-- Counts the number of elements in an object of type (Nested a).
count :: (Nested a) -> Int
count (Elem _) = 1
count (List x) = sum (map count x)

-- Concatenates two objects of type (Nested a).
-- Returns (Left "error") if one of the arguments is constructed from (Elem).
append :: (Nested a) -> (Nested a) -> Either String (Nested a)
append (List x) (List y) = Right (List (x ++ y))
append _        _        = Left  "error"

-- Unit test.
test_Nested :: IO ()
test_Nested = do
    test_count
    test_append
  where
    list_0 = List[Elem 1, Elem 2, List [Elem 3, Elem 4], List [Elem 5], Elem 6]
           --[1, 2, [3, 4], [5], 6]
    list_1 = List [List [], List [List [], List []]]
           --[[], [[], []]]
    test_count = do
      quickCheck $   6  ==  count list_0
      quickCheck $   0  ==  count list_1
    list_2 = List [Elem 1, Elem 2, Elem 3, Elem 4]
           --[1, 2, 3, 4]
    list_3 = List [Elem 5, Elem 6, Elem 7, Elem 8]
           --[5, 6, 7, 8]
    list_4 = List [Elem 1, Elem 2, Elem 3, Elem 4,
                   Elem 5, Elem 6, Elem 7, Elem 8]
           --[1, 2, 3, 4, 5, 6, 7, 8]
    list_5 = List [List [Elem 1, Elem 2], Elem 3]
           --[[1, 2], 3]
    list_6 = List [List [], Elem 5, List []]
           --[[], 5, []]
    list_7 = List [List [Elem 1, Elem 2], Elem 3, List [], Elem 5, List []]
           --[[1, 2], 3, [], 5, []]
    test_append = do
      quickCheck $   Right list_4 == append list_2 list_3
      quickCheck $   Right list_7 == append list_5 list_6



-- Trees -------------------------------

data Tree a = Empty
            | Branch a (Tree a) (Tree a)
            deriving (Show, Eq)

-- Private helper: Performs a standard recursive computation on a tree.
tree_fold :: (a -> b -> b -> b) -> b -> Tree a -> b
tree_fold f z = fold where
  fold Empty          = z
  fold (Branch e x y) = f e (fold x) (fold y)

-- Private helper function used by mindepth and maxdepth.
depth_function :: (Int -> Int -> Int) -> Tree a -> Int
depth_function f = tree_fold (\e n m -> 1 + f n m) 0

-- Computes the length of the shortest (resp. longest) path from root to leaf.
mindepth :: Tree a -> Int
mindepth = depth_function min
maxdepth :: Tree a -> Int
maxdepth = depth_function max

-- Inserts the given element into the given binary search tree.
-- (The given tree should be a well-formed binary search tree.)
tinsert :: Ord a => a -> Tree a -> Tree a
tinsert e1 Empty           = Branch e1 Empty     Empty
tinsert e1 (Branch e2 x y) = Branch e2 (f (<) x) (f (>) y) where
  f cmp x = if (e1 `cmp` e2) then (tinsert e1 x) else x

-- Unit test.
test_Tree :: IO ()
test_Tree = do
    test_mindepth
    test_maxdepth
    test_tinsert
  where
    tree_0 = Branch 10 (Branch 5 (Branch 3 Empty Empty) Empty) Empty
           -- [(3) 5 ()] 10 []
    tree_1 = Branch 10 (Branch 5 (Branch 3 Empty Empty) Empty)
             (Branch 11 Empty Empty)
           -- [(3) 5 ()] 10 [11]
    test_tinsert = do
      quickCheck $   tinsert 3  tree_0  ==  tree_0
      quickCheck $   tinsert 11 tree_0  ==  tree_1
    test_mindepth = do
      quickCheck $   1  ==  mindepth tree_0
      quickCheck $   2  ==  mindepth tree_1
    test_maxdepth = do
      quickCheck $   3  ==  maxdepth tree_0
      quickCheck $   3  ==  maxdepth tree_1



-- Entry point.

main = do
  test_Nested
  test_Tree
