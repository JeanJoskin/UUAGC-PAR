module ParSchedule (TaskTree (..), ParProfit, emptyTaskTree, sequentialTasks, taskTree, seqTaskTree, flatten, parProfits, mergeParProfits, decimate) where

import qualified Data.Graph as Graph
import Data.Graph.Inductive
import Data.Array (Array)
import qualified Data.Array as Array
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust,mapMaybe)
import Data.List (intersect,union,(\\),nub,sortBy,partition)
import System.IO.Unsafe
import Debug.Trace

import CodeSyntax
import GrammarInfo
import CommonTypes (Type (..),Identifier (..))
import SequentialTypes (getLhsNt,getCon,getField,getAttr,getType,getDefines,isChildVisit,ChildVisit (..))

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

profitTreshold = 5
profitUse = 2

emptyTaskTree :: TaskTree a
emptyTaskTree = TSeq 0 []

seqTaskTree :: Gr Node () -> [Node] -> TaskTree Node
seqTaskTree gr es = let sq = topsort' . remUnreach es $ gr
                    in  sequentialTasks sq

taskTree :: Array Node CRule -> Map Node ChildVisit -> Bool -> Gr Node () -> [Node] -> TaskTree Node
taskTree tbl vd dumpSched gr es =
     let dmpTT tt = vizTT' "ttdump" tt `seq` tt
         dmpG g = viz' "dump" g `seq` g
     in  dmpTT . rmZeroes . mkTaskTree' . dmpG . singleSource (-1) () . grev . remUnreach es $ gr

parProfits :: Ord a => Map a Int -> Int -> TaskTree a -> [ParProfit]
parProfits w s t = let accW = accNodeWeight w t
                       pfit = concatMap (oneParProfit accW s) (parNodes t)
                   in  take profitUse (sortParProfits pfit)

oneParProfit :: Map Int Int -> Int -> TaskTree a -> [ParProfit]
oneParProfit w s (TPar i cs) = let weight x = fromJust $ Map.lookup x w
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
                                  nodeWeight = sum $ map (fromJust . flip Map.lookup u . nodeIdent) cs
                              in  Map.insert i nodeWeight u
accNodeWeight w (TSeq i cs) = let u = Map.unions (map (accNodeWeight w) cs)
                                  nodeWeight = sum $ map (fromJust . flip Map.lookup u . nodeIdent) cs
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
                      d = cleanTaskTree $ decimate' parBranches t
                  in  vizTT' ("decim" ++ (show s)) d `seq` d

decimate' :: Show a => [Int] -> TaskTree a -> TaskTree a
decimate' ns (TSeq i cs) = let f [] = []
                               f (x:xs) = case (decimate' ns x) of
                                            (TPar i cs) ->
                                              let (a,b) = decimatePar ns x
                                              in  TPar i a : b ++ f xs
                                            _ -> x : f xs
                           in  TSeq i (f cs)
decimate' ns (TPar i cs) = TPar i (map (decimate' ns) cs)
decimate' ns n = n

decimatePar :: [Int] -> TaskTree a -> ([TaskTree a],[TaskTree a])
decimatePar ns (TPar i cs) = partition (flip elem ns . nodeIdent) cs

flatten :: TaskTree a -> [a]
flatten = foldTaskTree (const concat,const concat,const (flip (:) []))

sequentialTasks :: [a] -> TaskTree a
sequentialTasks xs = numTaskTree $ TSeq 0 (map (TTask 0) xs)

singleSource :: a -> b -> Gr a b -> Gr a b
singleSource nl el gr = let [s] = newNodes 1 gr
                            insS = insNode (s,nl)
                            insE = insEdges (map (\n -> (s,n,el)) (sources gr)) 
                        in  insE . insS $ gr

intersectGraph :: Gr a b -> Gr a b -> Gr a b
intersectGraph a b = let nodesA = nodes a
                         nodesB = nodes b
                         i = intersect (nodesA) (nodesB)
                     in  delNodes (nodesA \\ i) a

mkTaskNode :: Gr a b -> [TaskTree a] -> [Node] -> (Gr a b,[TaskTree a])
mkTaskNode g l []   = (g,l)
mkTaskNode g l [s]  = let g' = delNode s g
                          s' = filter (noDeps g') (suc g s)
                      in  mkTaskNode g' (TTask 0 (fromJust $ lab g s):l) s'
mkTaskNode g l ns   = let (graphs,children) = unzip $ map (\n -> mkTaskTree g [n]) ns
                          g' = foldr1 intersectGraph graphs
                          rm = unionMap nodes graphs \\ nodes g'
                          rmSucs = intersect (unionMap (suc g) rm) (nodes g')
                          s' = filter (noDeps g') rmSucs
                      in  mkTaskNode g' (TPar 0 children:l) s'

mkTaskTree :: Gr a b -> [Node] -> (Gr a b,TaskTree a)
mkTaskTree g s = let (g',l') = mkTaskNode g [] s
                 in  (g',TSeq 0 l')

mkTaskTree' :: Gr a b -> TaskTree a
mkTaskTree' g = let s = sources g
                    (g',t) = mkTaskTree g s
                in  if isEmpty g' then
                      numTaskTree t
                    else
                      error "The task graph is not acyclic"

foldTaskTree :: (Int -> [r] -> r,Int -> [r] -> r,Int -> a -> r) -> TaskTree a -> r
foldTaskTree (p,q,s) (TPar i a) = p i (map (foldTaskTree (p,q,s)) a)
foldTaskTree (p,q,s) (TSeq i a) = q i (map (foldTaskTree (p,q,s)) a)
foldTaskTree (p,q,s) (TTask i a)  = s i a

rmZeroes :: TaskTree Node -> TaskTree Node
rmZeroes = filterTaskTree ((/=) (-1))

remUnreach :: [Node] -> Gr a b -> Gr a b
remUnreach ns gr = let rch = dfs ns gr
                       ur  = filter (flip notElem rch) (nodes gr)
                   in  delNodes ur gr

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
graphToGr :: Graph.Graph -> Gr Int ()
graphToGr g = mkGraph (map (\n -> (n,n)) (Graph.vertices g)) (map (\(a,b) -> (a,b,())) (Graph.edges g))

grToGraph :: Gr a b -> Graph.Graph
grToGraph gr = Graph.buildG (nodeRange gr) (edges gr)

combine :: [a] -> [[a]]
combine []     = []
combine (x:xs) = foldr (\y -> (:) [x,y]) (combine xs) xs

viz :: (Show a, Show b) => String -> Gr a b -> IO ()
viz nm gr = let content = graphviz gr "" (0,0) (0,0) Portrait
            in  writeFile (nm ++ ".dot") content

viz' :: (Show a, Show b) => String -> Gr a b -> ()
viz' nm gr = unsafePerformIO (viz nm gr)

vizTT :: Show a => String -> TaskTree a -> IO ()
vizTT nm tt = writeFile (nm ++ ".dot") (vizTree tt)

vizTT' :: Show a => String -> TaskTree a -> ()
vizTT' nm tt = unsafePerformIO (vizTT nm tt)

sources :: Gr a b -> [Node]
sources gr = filter (\n -> indeg gr n == 0) (nodes gr)

noDeps :: Gr a b -> Node -> Bool
noDeps g n = indeg g n == 0

unionMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionMap f xs = nub (concatMap f xs)

filterTaskTree :: (a -> Bool) -> TaskTree a -> TaskTree a
filterTaskTree f (TTask i x) = TTask i x
filterTaskTree f (TPar i xs) = TPar i $ map (filterTaskTree f) (fltTT f xs)
filterTaskTree f (TSeq i xs) = TSeq i $ map (filterTaskTree f) (fltTT f xs)

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
                                          in  (n',(x':r))
                              (num',xsR') = foldl f (num,[]) xsR
                          in  (num' + 1,c num' xsR')

nodeIdent :: TaskTree a -> Int
nodeIdent (TPar i _) = i
nodeIdent (TSeq i _) = i
nodeIdent (TTask i _) = i

vizTree :: Show a => TaskTree a -> String
vizTree t = "digraph G {\n" ++
              "ordering = out\n" ++
              vizLabels t ++
              vizEdges t ++
              "}"

vizLabels :: Show a => TaskTree a -> String
vizLabels (TPar i xs) = (show i) ++ " [label =\"Par\"]\n" ++ concatMap vizLabels xs
vizLabels (TSeq i xs) = (show i) ++ " [label =\"Seq\"]\n" ++ concatMap vizLabels xs
vizLabels (TTask i n) = (show i) ++ " [label =\"" ++ show n ++ "\",shape=box]\n"

vizEdges :: Show a => TaskTree a -> String
vizEdges (TPar i xs) = concatMap (\x -> (show i) ++ " -> " ++ (show $ nodeIdent x) ++ "\n") xs
                        ++ concatMap vizEdges xs
vizEdges (TSeq i xs) = concatMap (\x -> (show i) ++ " -> " ++ (show $ nodeIdent x) ++ "\n") xs
                        ++ concatMap vizEdges xs
vizEdges (TTask i n) = ""
