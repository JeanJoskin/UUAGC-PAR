module GraphDump
  (vizG'
  ,vizTT'
  ,simplifyG
  ) where

import Data.Graph
import Data.Array
import System.IO.Unsafe
import TaskTree

-- Dumping graphs

vizG :: String -> (Vertex -> String) -> Graph -> IO ()
vizG nm lbl g = writeFile (nm ++ ".dot") (vizGraph lbl g)

vizG' :: String -> (Vertex -> String) -> Graph -> Graph
vizG' nm lbl g = unsafePerformIO (vizG nm lbl g) `seq` g

vizGraph :: (Vertex -> String) -> Graph -> String
vizGraph lbl g = "digraph G {\n" ++
                 vizGLabels lbl g ++
                 vizGEdges g ++
                 "}"

vizGEdges :: Graph -> String
vizGEdges = concatMap (\(a,b) -> show a ++ " -> " ++ show b ++ "\n") . edges

vizGLabels :: (Vertex -> String) -> Graph -> String
vizGLabels f g = concatMap (\v -> show v ++ " [label =\"" ++ f v ++ "\"]\n") (vertices g)

-- Task Trees

vizTT :: String -> (a -> String) -> TaskTree a -> IO ()
vizTT nm lbl tt = writeFile (nm ++ ".dot") (vizTree lbl tt)

vizTT' :: String -> (a -> String) -> TaskTree a -> TaskTree a
vizTT' nm lbl tt = unsafePerformIO (vizTT nm lbl tt) `seq` tt


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

simplifyG :: Graph -> Graph
simplifyG g = let es' = filterTrans [] (bounds g) (edges g)
              in  buildG (bounds g) (es')

filterTrans :: [(Vertex,Vertex)] -> (Int,Int) -> [(Vertex,Vertex)] -> [(Vertex,Vertex)]
filterTrans es' b [] = es'
filterTrans es' b ((p,q):es) = let g = buildG b (es' ++ es)
                               in  if path g p q
                                   then filterTrans es' b es
                                   else filterTrans ((p,q):es') b es
