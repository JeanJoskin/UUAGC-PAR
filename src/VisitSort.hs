{-# OPTIONS_GHC -XRank2Types #-}
module VisitSort(visitSort) where
	
import Data.Graph(Vertex, Graph, Forest (..), Bounds)
import Data.Tree(Tree(Node), rootLabel)
import Data.Array ((!),bounds)
import Data.List(sortBy)
import Control.Monad.ST
import Data.Array.ST (STArray, newArray, readArray, writeArray)

postorder :: Tree Vertex -> [Vertex]
postorder (Node a ts) = postorderF ts ++ [a]

postorderF :: Forest Vertex -> [Vertex]
postorderF = concatMap postorder

postOrd :: (Vertex -> Bool) -> Graph -> [Vertex] -> [Vertex]
postOrd isCv g = postorderF . dfsVisitFirst isCv g

visitSort :: (Vertex -> Bool) -> Graph -> [Vertex] -> [Vertex]
visitSort = postOrd

--

dfsVisitFirst :: (Vertex -> Bool) -> Graph -> [Vertex] -> Forest Vertex
dfsVisitFirst isCv g vs = let dfs    = map (generate g) vs
                              count  = map (countTree isCv) dfs
                              sorted = zipWith sortTree dfs count
                              pruned = prune (bounds g) sorted
                          in pruned


generate :: Graph -> Vertex -> Tree Vertex
generate g v  = Node v (map (generate g) (g!v))

countTree :: (Vertex -> Bool) -> Tree Vertex -> Tree Int
countTree isCv (Node a ts) = let ts' = map (countTree isCv) ts
                                 c   = sum $ map rootLabel ts
                                 c'  | isCv a    = c
                                     | otherwise = 1 + c
                             in Node c' ts'

sortTree :: Tree Vertex -> Tree Int -> Tree Vertex
sortTree (Node a ts) (Node _ cs) = let z = zip ts cs
                                       s = sortBy (\a b -> compare (rootLabel $ snd b) (rootLabel $ snd a)) z
                                       r = map fst s
                                   in Node a r


-- Below: Copied from Data.Graph

newtype SetM s a = SetM { runSetM :: STArray s Vertex Bool -> ST s a }

instance Monad (SetM s) where
    return x     = SetM $ const (return x)
    SetM v >>= f = SetM $ \ s -> do { x <- v s; runSetM (f x) s }

run          :: Bounds -> (forall s. SetM s a) -> a
run bnds act  = runST (newArray bnds False >>= runSetM act)

contains     :: Vertex -> SetM s Bool
contains v    = SetM $ \ m -> readArray m v

include      :: Vertex -> SetM s ()
include v     = SetM $ \ m -> writeArray m v True

prune        :: Bounds -> Forest Vertex -> Forest Vertex
prune bnds ts = run bnds (chop ts)

chop         :: Forest Vertex -> SetM s (Forest Vertex)
chop []       = return []
chop (Node v ts : us)
              = do
                visited <- contains v
                if visited then
                  chop us
                 else do
                  include v
                  as <- chop ts
                  bs <- chop us
                  return (Node v as : bs) 