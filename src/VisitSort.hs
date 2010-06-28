{-# OPTIONS_GHC -XRank2Types #-}
module VisitSort(visitSort) where
	
import Data.Graph(Vertex, Graph, Forest (..), Bounds)
import Data.Tree(Tree(Node))
import Data.Array ((!),bounds)

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
dfsVisitFirst isCv g vs = prune (bounds g) (map (snd . (generate isCv g)) vs)

generate     :: (Vertex -> Bool) -> Graph -> Vertex -> (Bool,Tree Vertex)
generate isCv g v  = let genBranch []     = (False,[])
                         genBranch (x:xs) = let (c,t)   = generate isCv g x
                                                (c',t') = genBranch xs
                                                c2      = c || c'
                                                t2      | c         = t:t'
                                                        | otherwise = t' ++ [t]
                                            in (c2, t2)
                         (c,t)            = genBranch (g!v)
                     in (c || isCv v, Node v t)

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