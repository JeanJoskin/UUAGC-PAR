module ParSchedule (TaskTree (..), ParProfit, emptyTaskTree, sequentialTasks, taskTree, seqTaskTree, flatten, parProfits, mergeParProfits, decimate, filterTaskTree') where

import Data.Graph
import Data.Array (Array)
import qualified Data.Array as Array
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.List (intersect,union,(\\),nub,sortBy,partition)
import qualified Data.Tree as Tree

import CodeSyntax (CRule)
import CommonTypes (Type (..),Identifier (..))
import SequentialTypes (ChildVisit (..))

import System.IO.Unsafe
import Debug.Trace

data ParProfit = ParProfit {
                      profit :: Int,
                      scope  :: Int,
                      branches :: [Int]
                 }
                 deriving Show

data TaskTree a = TPar Int [TaskTree a]
                | TSeq Int [TaskTree a]
                | TTask Int a
                deriving (Show)

profitTreshold = 1
profitUse = 2

emptyTaskTree :: TaskTree a
emptyTaskTree = TSeq 0 []

seqTaskTree :: Bool -> (Vertex -> String) -> Graph -> String -> [Vertex] -> TaskTree Vertex
seqTaskTree dump lbl gr prettyName es =
    let dmpTT tt | dump = vizTT' (prettyName ++ "-tt") lbl tt
                 | otherwise = tt
        dmpG g | dump = vizG' (prettyName ++ "-g") lbl g
               | otherwise = g
    in  dmpTT $ sequentialTasks $ flatten $ taskTree False lbl (dmpG gr) prettyName es

taskTree :: Bool -> (Vertex -> String) -> Graph -> String -> [Vertex] -> TaskTree Vertex
taskTree dump lbl gr prettyName es =
     let dmpTT tt | dump = vizTT' (prettyName ++ "-tt") lbl tt
                  | otherwise = tt
         dmpG g   | dump = vizG' (prettyName ++ "-g") lbl g
                  | otherwise = g
     in  dmpTT . mkTaskTree' es . dmpG $ gr

parProfits :: Ord a => Map a Int -> Int -> TaskTree a -> [ParProfit]
parProfits w s t = let accW = accNodeWeight w t
                       pfit = concatMap (oneParProfit accW s) (parNodes t)
                   in  take profitUse (sortParProfits pfit)

oneParProfit :: Map Int Int -> Int -> TaskTree a -> [ParProfit]
oneParProfit w s (TPar i cs) = let weight x = w Map.! x
                                   f [a,b] = let ai = nodeIdent a
                                                 bi = nodeIdent b
                                                 wa = weight ai
                                                 wb = weight bi
                                                 p  = (wa + wb) - (max wa wb)
                                             in  if p >= profitTreshold
                                                   then Just $ ParProfit p s [ai,bi]
                                                   else Nothing
                               in  mapMaybe f (combine cs)

mergeParProfits :: [ParProfit] -> [ParProfit] -> [ParProfit]
mergeParProfits a b = take profitUse (sortParProfits (a ++ b))

sortParProfits :: [ParProfit] -> [ParProfit]
sortParProfits = sortBy (\a b -> compare (profit b) (profit a))

accNodeWeight :: Ord a => Map a Int -> TaskTree a -> Map Int Int
accNodeWeight w (TPar i cs) = let u = Map.unions (map (accNodeWeight w) cs)
                                  nodeWeight = sum $ map ((Map.!) u . nodeIdent) cs
                              in  Map.insert i nodeWeight u
accNodeWeight w (TSeq i cs) = let u = Map.unions (map (accNodeWeight w) cs)
                                  nodeWeight = sum $ map ((Map.!) u . nodeIdent) cs
                              in  Map.insert i nodeWeight u
accNodeWeight w (TTask i n) = Map.insert i (Map.findWithDefault 1 n w) Map.empty

parNodes :: TaskTree a -> [TaskTree a]
parNodes n = case n of
               (TPar _ cs) -> n : concatMap parNodes cs
               (TSeq _ cs) -> concatMap parNodes cs
               _           -> []

decimate :: Show a => [ParProfit] -> Int -> TaskTree a -> TaskTree a
decimate ps s t = let inScope = filter (\p -> scope p == s) ps
                      parBranches = concatMap branches inScope
                      decim = cleanTaskTree $ decimate' parBranches t
                  in  decim

decimate' :: Show a => [Int] -> TaskTree a -> TaskTree a
decimate' ns (TSeq i cs) = let f [] = []
                               f (x:xs) = case (decimate' ns x) of
                                            (TPar pi pcs) ->
                                              let (a,b) = partition (flip elem ns . nodeIdent) pcs
                                              in  TPar pi a : b ++ f xs
                                            _ -> x : f xs
                           in  TSeq i (f cs)
decimate' ns (TPar i cs) = TPar i (map (decimate' ns) cs)
decimate' ns n = n

flatten :: TaskTree a -> [a]
flatten = foldTaskTree (const concat,const concat,const (\x -> [x]))

sequentialTasks :: [a] -> TaskTree a
sequentialTasks xs = numTaskTree $ TSeq 0 (map (TTask 0) xs)

releasedVertices :: Graph -> [Vertex] -> [Vertex] -> [Vertex]
releasedVertices g i ns = let preds = nub $ filter (not . null . intersect ns . (Array.!) g) i
                          in  filter (isSink g i) preds

mkTaskNode :: Graph -> [Vertex] -> [TaskTree Vertex] -> [Vertex] -> ([Vertex],[TaskTree Vertex])
mkTaskNode g i l []   = (i,l)
mkTaskNode g i l [s]  = let i' = i \\ [s]
                            s' = releasedVertices g i' [s]
                        in  mkTaskNode g i' (TTask 0 s:l) s'
mkTaskNode g i l ns   = let (is,children) = unzip $ map (\n -> mkTaskTree g i [n]) ns
                            i' = foldr1 intersect is
                            s' = releasedVertices g i' (i \\ i')
                        in  mkTaskNode g i' (TPar 0 children:l) s'

mkTaskTree :: Graph -> [Vertex] -> [Vertex] -> ([Vertex],TaskTree Vertex)
mkTaskTree g i s = let (i',l') = mkTaskNode g i [] s
                   in  (i',TSeq 0 (reverse l'))

mkTaskTree' :: [Vertex] -> Graph -> TaskTree Vertex
mkTaskTree' s g = let i = concatMap Tree.flatten (dfs g s)
                      (i',t) = mkTaskTree g i (sinks g i)
                  in  if null i' then
                        numTaskTree t
                      else
                        error "The task graph is not acyclic"

sinks :: Graph -> [Vertex] -> [Vertex]
sinks g i = filter (isSink g i) i

isSink :: Graph -> [Vertex] -> Vertex -> Bool
isSink g i v = null (intersect i (g Array.! v))

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

-- Utility functions
combine :: [a] -> [[a]]
combine []     = []
combine (x:xs) = foldr (\y -> (:) [x,y]) (combine xs) xs

vizTT :: String -> (a -> String) -> TaskTree a -> IO ()
vizTT nm lbl tt = writeFile (nm ++ ".dot") (vizTree lbl tt)

vizTT' :: String -> (a -> String) -> TaskTree a -> TaskTree a
vizTT' nm lbl tt = unsafePerformIO (vizTT nm lbl tt) `seq` tt

vizG :: String -> (Vertex -> String) -> Graph -> IO ()
vizG nm lbl g = writeFile (nm ++ ".dot") (vizGraph lbl g)

vizG' :: String -> (Vertex -> String) -> Graph -> Graph
vizG' nm lbl g = unsafePerformIO (vizG nm lbl g) `seq` g

unionMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionMap f xs = nub (concatMap f xs)

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

vizTree :: (a -> String) -> TaskTree a -> String
vizTree lbl t = "digraph G {\n" ++
                 "ordering = out\n" ++
                 vizTLabels lbl t ++
                 vizTEdges t ++
                 "}"

vizTLabels :: (a -> String) -> TaskTree a -> String
vizTLabels lbl (TPar i xs) = (show i) ++ " [label =\"Par\"]\n" ++ concatMap (vizTLabels lbl) xs
vizTLabels lbl (TSeq i xs) = (show i) ++ " [label =\"Seq\"]\n" ++ concatMap (vizTLabels lbl) xs
vizTLabels lbl (TTask i n) = (show i) ++ " [label =\"" ++ lbl n ++ "\",shape=box]\n"

vizTEdges :: TaskTree a -> String
vizTEdges (TPar i xs) = concatMap (\x -> (show i) ++ " -> " ++ (show $ nodeIdent x) ++ "\n") xs
                        ++ concatMap vizTEdges xs
vizTEdges (TSeq i xs) = concatMap (\x -> (show i) ++ " -> " ++ (show $ nodeIdent x) ++ "\n") xs
                        ++ concatMap vizTEdges xs
vizTEdges (TTask i n) = ""


vizGraph :: (Vertex -> String) -> Graph -> String
vizGraph lbl g = "digraph G {\n" ++
                 vizGLabels lbl g ++
                 vizGEdges g ++
                 "}"

vizGEdges :: Graph -> String
vizGEdges = concatMap (\(a,b) -> show a ++ " -> " ++ show b ++ "\n") . edges

vizGLabels :: (Vertex -> String) -> Graph -> String
vizGLabels f g = concatMap (\v -> show v ++ " [label =\"" ++ f v ++ "\"]\n") (vertices g)

