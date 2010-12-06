module GraphDump
  (GraphDumps
  ,vizG'
  ,vizTT'
  ,vizTds
  ,showRule
  ,showAttr
  ) where

import SequentialTypes hiding (Vertex,Table)
import CommonTypes (getName)
import CodeSyntax (CRule)
import GrammarInfo
import qualified Data.Map as Map
import Data.Map (Map)

import Data.Graph
import Data.Array
import Data.List (intersperse)
import System.IO.Unsafe
import TaskTree

type GraphDumps = [(String,String)]

type MGraph    = Array     Vertex (Map.Map Vertex Path)

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

vizGLabels :: (Vertex -> String) -> Array Vertex a -> String
vizGLabels f g = concatMap (\v -> show v ++ " [label =\"" ++ f v ++ "\"]\n") (indices g)

vizMGraph :: Info -> (Vertex -> String) -> MGraph -> String
vizMGraph info lbl g = "digraph G {\n" ++
                       vizGLabels lbl g ++
                       vizMGEdges info g ++
                       "}"

vizMGEdges :: Info -> MGraph -> String
vizMGEdges info = concatMap (\(a,(b,p)) -> show a ++ " -> " ++ show b ++ mEdgeLayout info (a,(b,p)) ++ "\n") . edgesM

mEdgeLayout info (a,(b,p)) = let attr = attrTable info
                                 style = case p of
                                           [AtOcStep _ _] -> "style=solid"
                                           _              -> "style=dashed"
                                 color = case (attr ! a) of
                                           (NTAInh _ _ _) ->
                                             case (attr ! b) of
                                               (NTAInh _ _ _) -> "color=black"
                                               (NTASyn _ _ _) -> "color=forestgreen"
                                           (NTASyn _ _ _) ->
                                              case (attr ! b) of
                                                (NTAInh _ _ _) -> "color=firebrick"
                                                (NTASyn _ _ _) -> "color=black"
                             in " [" ++ style ++ "," ++ color ++ ",label=\"" ++ (showEdge p) ++  "\"]"

showEdge :: Path -> String
showEdge = let f (AttrStep a b) = show a ++ ">" ++ show b
           in  concat . intersperse "," . map f . filter isAttrStep

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
                               in  if p == q || path g p q
                                   then filterTrans es' b es
                                   else filterTrans ((p,q):es') b es

simplifyMG :: MGraph -> MGraph
simplifyMG g = let es' = filterMTrans [] (bounds g) (edgesM g)
               in  buildMG (bounds g) es'


edgesM :: MGraph -> [(Vertex,(Vertex,Path))]
edgesM g = [ (v, w) | v <- indices g, w <- Map.assocs (g ! v) ]

buildMG :: Bounds -> [(Vertex,(Vertex,Path))] -> MGraph
buildMG = accumArray (\m (q,r) -> Map.insert q r m) Map.empty

filterMTrans :: [(Vertex,(Vertex,Path))] -> (Int,Int) -> [(Vertex,(Vertex,Path))] -> [(Vertex,(Vertex,Path))]
filterMTrans es' b [] = es'
filterMTrans es' b ((p,(q,r)):es) = let g = buildG b (map (\(p,(q,r)) -> (p,q)) (es' ++ es))
                                    in  if p == q || path g p q
                                        then filterMTrans es' b es
                                        else filterMTrans ((p,(q,r)):es') b es

vizTds :: Info -> MGraph -> String
vizTds info g = vizMGraph info (showAttr (attrTable info)) (simplifyMG g)

vizTdp :: Table CRule -> MGraph -> MGraph
vizTdp r g = vizG' "tdp" (show) (fmap Map.keys g) `seq` g

isAttrStep (AttrStep _ _) = True
isAttrStep _ = False

showAttr :: Table NTAttr -> Int -> String
showAttr attrTable i = show (attrTable ! i) ++ " / " ++ show i

shortChildVisit :: ChildVisit -> String
shortChildVisit (ChildVisit fld rhsNt nr inhs syns) = (getName rhsNt) ++ "." ++ (getName fld) ++ " #" ++ (show nr)

shortCRule :: CRule -> String
shortCRule r = (show $ getLhsNt r) ++ "." ++ (show $ getCon r)++ "." ++ (show $ getField r) ++ "." ++ (show $ getAttr r)

showRule :: Table CRule -> Map Vertex ChildVisit -> Vertex -> String
showRule tbl vd v | inRange (bounds tbl) v = shortCRule (tbl ! v) ++ " (" ++ (show v) ++ ")"
                     | Map.member v vd        = shortChildVisit (vd Map.! v) ++ " (" ++ (show v) ++ ")" 
                     | otherwise              = (show v)
