module TaskTree
  (TaskTree (..)
  ,cleanTaskTree
  ,emptyTaskTree
  ,numTaskTree
  ,filterTaskTree'
  ,flatten
  ,nodeIdent
  ) where

data TaskTree a = TPar Int [TaskTree a]
                | TSeq Int [TaskTree a]
                | TTask Int a
                deriving (Show)

emptyTaskTree :: TaskTree a
emptyTaskTree = TSeq 0 []

foldTaskTree :: (Int -> [r] -> r,Int -> [r] -> r,Int -> a -> r) -> TaskTree a -> r
foldTaskTree (p,q,s) (TPar i a) = p i (map (foldTaskTree (p,q,s)) a)
foldTaskTree (p,q,s) (TSeq i a) = q i (map (foldTaskTree (p,q,s)) a)
foldTaskTree (p,q,s) (TTask i a)  = s i a

instance Functor TaskTree where
  fmap f = foldTaskTree (TPar,TSeq,(\i x -> TTask i (f x)))

cleanTaskTree :: TaskTree a -> TaskTree a
cleanTaskTree (TPar i cs) = let up c = (not (isTask c)) && (isPar c || null (nodeChildren c))
                                f [] = []
                                f (x:xs) | up x = nodeChildren x ++ f xs
                                         | otherwise = x : f xs
                            in  TPar i (map cleanTaskTree (f cs))
cleanTaskTree (TSeq i cs) = let up c = (not (isTask c)) && (isSeq c || null (nodeChildren c))
                                f [] = []
                                f (x:xs) | up x = nodeChildren x ++ f xs
                                         | otherwise = x : f xs
                            in  TSeq i (map cleanTaskTree (f cs))
cleanTaskTree n = n

nodeChildren (TPar i cs) = cs
nodeChildren (TSeq i cs) = cs
nodeChildren _ = []

isTask (TTask i n) = True
isTask _ = False

isSeq (TSeq i cs) = True
isSeq _ = False

isPar (TPar i cs) = True
isPar _ = False

filterTaskTree :: (a -> Bool) -> TaskTree a -> TaskTree a
filterTaskTree f (TTask i x) = TTask i x
filterTaskTree f (TPar i xs) = TPar i $ map (filterTaskTree f) (fltTT f xs)
filterTaskTree f (TSeq i xs) = TSeq i $ map (filterTaskTree f) (fltTT f xs)

filterTaskTree' :: (a -> Bool) -> TaskTree a -> TaskTree a
filterTaskTree' f = cleanTaskTree . filterTaskTree f

fltTT :: (a -> Bool) -> [TaskTree a] -> [TaskTree a]
fltTT f xs = let f' x = case (x) of
                          (TTask i n) -> f n
                          _           -> True
             in  filter f' xs

type Num_Result a = Int -> (Int,TaskTree a)

numTaskTree :: TaskTree a -> TaskTree a
numTaskTree t = snd (numTaskTree' t 1)

numTaskTree' :: TaskTree a -> Num_Result a
numTaskTree' (TPar i xs) = numTaskNode TPar i (map numTaskTree' xs)
numTaskTree' (TSeq i xs) = numTaskNode TSeq i (map numTaskTree' xs)
numTaskTree' (TTask i n) = \num -> (num + 1, TTask num n)

numTaskNode :: (Int -> [TaskTree a] -> TaskTree a) -> Int -> [Num_Result a] -> Num_Result a
numTaskNode c i xsR num = let f (n,r) x = let (n',x') = x n
                                          in  (n',(r ++ [x']))
                              (num',xsR') = foldl f (num,[]) xsR
                          in  (num' + 1,c num' xsR')

nodeIdent :: TaskTree a -> Int
nodeIdent (TPar i _) = i
nodeIdent (TSeq i _) = i
nodeIdent (TTask i _) = i


flatten :: TaskTree a -> [a]
flatten = foldTaskTree (const concat,const concat,const (\x -> [x]))
