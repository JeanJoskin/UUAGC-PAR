module ParSchedule 
  (TaskTree (..)
  , ParProfit
  , sequentialTasks
  , taskTree
  , seqTaskTree
  , parProfits
  , mergeParProfits
  , decimate
  ) where

import Data.Graph
import Data.Array (Array)
import qualified Data.Array as Array
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.List (intersect,union,(\\),nub,sortBy,partition)
import qualified Data.Tree as Tree
import Control.DeepSeq

import CodeSyntax (CRule)
import CommonTypes (Type (..),Identifier (..))
import SequentialTypes (ChildVisit (..))
import GraphDump
import TaskTree

import Debug.Trace

data ParProfit = ParProfit {
                      profit :: Int,
                      scope  :: Int,
                      branches :: [Int]
                 }
                 deriving Show

profitTreshold = 1
profitUse = 2

seqTaskTree :: Graph -> (Vertex -> String) -> Maybe String -> [Vertex] -> TaskTree Vertex
seqTaskTree gr lbl dumpPrefix es =
    let dmpTT tt = case dumpPrefix of
                      (Just prefix) -> vizTT' (prefix ++ "-tt") lbl tt
                      _             -> tt
        dmpG g = case dumpPrefix of
                   (Just prefix) -> vizG' (prefix ++ "-g") lbl g
                   _             -> g
    in  dmpTT $ sequentialTasks $ flatten $ taskTree (dmpG gr) lbl Nothing es

taskTree :: Graph -> (Vertex -> String) -> Maybe String -> [Vertex] -> TaskTree Vertex
taskTree gr lbl dumpPrefix es =
     let dmpTT tt = case dumpPrefix of
                      (Just prefix) -> vizTT' (prefix ++ "-tt") lbl tt
                      _             -> tt
         dmpG g = case dumpPrefix of
                    (Just prefix) -> vizG' (prefix ++ "-g") lbl g
                    _             -> g
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

decimate :: Show a => (Vertex -> String) -> [ParProfit] -> Maybe String -> Int -> TaskTree a -> TaskTree a
decimate lbl ps dumpPrefix s t =
    let inScope = filter (\p -> scope p == s) ps
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
                      numT = numTaskTree t
                  in  if null i' then
                        numT `deepseq` numT
                      else
                        error "The task graph is not acyclic"

sinks :: Graph -> [Vertex] -> [Vertex]
sinks g i = filter (isSink g i) i

isSink :: Graph -> [Vertex] -> Vertex -> Bool
isSink g i v = null (intersect i (g Array.! v))

-- Utility functions
combine :: [a] -> [[a]]
combine []     = []
combine (x:xs) = foldr (\y -> (:) [x,y]) (combine xs) xs

unionMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionMap f xs = nub (concatMap f xs)
