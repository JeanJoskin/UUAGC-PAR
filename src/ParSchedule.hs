module ParSchedule (parSchedule,seqSchedule,ParTree (..),flattenParTree,filterParTree,foldParTree,cleanParTree,parTree,PSTree,parGains) where

import qualified Data.Array as Array
import Data.Graph.Inductive
import Data.Graph.Inductive.Query.DFS (topsort')
import Data.Graph.Inductive.Query.TransClos
import qualified Data.Graph as Graph
import Data.Graph.Inductive.Graphviz

import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Data.Maybe (fromJust,mapMaybe,isJust)
import Data.List (find,findIndex,nub,minimumBy,sortBy,intersect,partition,union,(\\))

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Tree (Tree (..),Forest)

import Debug.Trace
import System.IO.Unsafe

import CodeSyntax
import GrammarInfo
import CommonTypes (Type (..),Identifier (..))
import SequentialTypes (getLhsNt,getCon,getField,getAttr,getType,getDefines,isChildVisit,ChildVisit (..))
import Data.Array (Array)

-- Utility functions

graphToGr :: Graph.Graph -> Gr Int ()
graphToGr g = mkGraph (map (\n -> (n,n)) (Graph.vertices g)) (map (\(a,b) -> (a,b,())) (Graph.edges g))

grToGraph :: Gr a b -> Graph.Graph
grToGraph gr = Graph.buildG (nodeRange gr) (edges gr)

remUnreach :: [Node] -> Gr a b -> Gr a b
remUnreach ns gr = let rch = dfs ns gr
                       ur  = filter (flip notElem rch) (nodes gr)
                   in  delNodes ur gr

viz :: (Show a, Show b) => String -> Gr a b -> IO ()
viz nm gr = let content = graphviz gr "" (0,0) (0,0) Portrait
            in  writeFile (nm ++ ".dot") content

viz' :: (Show a, Show b) => String -> Gr a b -> ()
viz' nm gr = unsafePerformIO (viz nm gr)

hasLEdge :: LEdge c -> Gr a b -> Bool
hasLEdge (a,b,_) gr = elem b (suc gr a)

hasEdge :: Edge -> Gr a b -> Bool
hasEdge (a,b) gr = elem b (suc gr a)

combine :: [a] -> [[a]]
combine []     = []
combine (x:xs) = foldr (\y -> (:) [x,y]) (combine xs) xs

sources :: Gr a b -> [Node]
sources gr = filter (\n -> indeg gr n == 0) (nodes gr)

rmELabel :: LEdge a -> Edge
rmELabel (a,b,_) = (a,b)

rmELabels = map rmELabel

splits :: Gr a b -> [Node]
splits gr = filter (\n -> outdeg gr n > 1) (nodes gr)

nfilter :: (Node -> Bool) -> Gr a b -> Gr a b
nfilter f gr = delNodes (filter (not . f) (nodes gr)) gr

nearestJoin :: TopOrd -> [Node] -> Maybe Node
nearestJoin to ns | null ns   = Nothing
                  | otherwise = Just (minimumBy to ns)

topOrd' :: IntMap Int -> Node -> Node -> Ordering
topOrd' t a b = compare (IntMap.lookup a t) (IntMap.lookup b t)

mkTopOrd :: Gr a b -> TopOrd
mkTopOrd gr = let t = topsort gr
                  m = IntMap.fromList (zip t [1..])
              in  topOrd' m

nodesBetween :: Gr a () -> Node -> Node -> [Node]
nodesBetween tc s j = intersect (filter ((/=) s) (suc tc s)) (filter ((/=) j) (pre tc j))

-- Types

data ParTree a = TPar (ParTree a) (ParTree a)
               | TSeq (ParTree a) (ParTree a)
               | TSingle a
               | TNone
               deriving (Show,Eq)

data SplitJoin = SJ { sjSplit :: Node,
                      sjBranches :: Set Node,
                      sjBetween :: [Node],
                      sjJoin :: Node } deriving (Show,Eq)

data EdgeType = Seq | Par deriving (Show,Eq)

type TopOrd = Node -> Node -> Ordering

type PSTree = Gr Node EdgeType

-- Transformation functions

shortChildVisit :: ChildVisit -> String
shortChildVisit (ChildVisit fld rhsNt nr inhs syns) = (getName rhsNt) ++ "." ++ (getName fld) ++ " #" ++ (show nr)

shortCRule :: CRule -> String
shortCRule r = (show $ getLhsNt r) ++ "." ++ (show $ getCon r)++ "." ++ (show $ getField r) ++ "." ++ (show $ getAttr r)

labelNodes :: Array Node CRule -> Map Node ChildVisit -> Gr Int b -> Gr String b
labelNodes tbl vd gr = let lbl (Just v) | Array.inRange (Array.bounds tbl) v = shortCRule (tbl Array.! v) ++ " (" ++ (show v) ++ ")"
                                        | Map.member v vd                    = shortChildVisit (fromJust $ Map.lookup v vd) ++ " (" ++ (show v) ++ ")" 
                                        | otherwise                          = (show v)
                           lbl Nothing = "?"
                       in nmap (lbl . lab gr) gr

dump :: (Show b) => Array Node CRule -> Map Node ChildVisit -> String -> String -> Gr Int b -> Gr Int b
dump tbl vd pnm nm gr = viz' (pnm ++ '-':nm) (labelNodes tbl vd gr) `seq` gr

seqSchedule :: Gr Node () -> [Node] -> PSTree
seqSchedule gr es = let seqGraph ns = mkGraph (zip ns ns) (zipWith (\a b -> (a,b,Par)) (init ns) (tail ns))
                    in  seqGraph . topsort' . grev . remUnreach es $ gr

parSchedule :: Array Node CRule -> Map Node ChildVisit -> Bool -> Gr Node () -> [Node] -> PSTree
parSchedule tbl vd dumpSched gr es = 
    let dmp nm | dumpSched = dump tbl vd (show es) nm
               | otherwise = id
        gr' = dmp "2-remrev" . grev . remUnreach es . dmp "1-in" $ gr
        s   = head (newNodes 1 gr')
        gr'' = insEdges (map (\n -> (s,n,())) (sources gr')) . insNode (s,-1) $ gr'
    in  dmp "7-tree" . taskTree . dmp "6-split" . splitTaskGraph . dmp "5-clean" . clean . dmp "4-lin" . linearize . dmp "3-clean" . clean . remDups tbl s $ gr''

balanceTake = 1
balanceTreshold = 5

{-
balancedParTree :: Map Node Int -> PSTree -> ParTree Node
balancedParTree gr = let ss = splits gr
                         gains = filter ((>) balanceTreshold . fst) (concatMap (parGains vw gr) ss)
                          topGains = sortBy (\a b -> compare (fst a) (fst b)) gains
                            selGains = take balanceTake topGains
                            seqEdges = concatMap snd selGains
                        in  trace (show seqEdges) $ parTree' (Set.fromList seqEdges) gr
-}

weight :: Map Node Int -> Node -> Int
weight vw n = case (Map.lookup n vw) of
                (Just w) -> w
                _        -> 0

parGain1 :: Map Node Int -> PSTree -> [Node] -> Int
parGain1 vw gr [a,b] = let w x = foldr ((+) . weight vw) 0 (dfs [x] gr)
                           wa = w a
                           wb = w b
                       in  (wa + wb) - (max wa wb)
    
parGains1 :: Map Node Int -> PSTree -> Node -> [(Int,[Node])]
parGains1 vw gr s = let pBranches = map fst $ filter ((==) Par . snd) $ lsuc gr s
                        pairs = combine pBranches
                    in  zip (map (parGain1 vw gr) pairs) pairs

parGains :: Map Node Int -> PSTree -> [(Int,[Node])]
parGains vw gr = let ss = splits gr
                     gains = concatMap (parGains1 vw gr) ss
                     gains' = filter ((<) balanceTreshold . fst) gains
                 in  sortBy (\a b -> compare (fst a) (fst b)) gains'

parTree' :: PSTree -> ParTree Node
parTree' = parTree Set.empty

parTree :: Set Node -> PSTree -> ParTree Node
parTree sq = remTempNodes . mkParTree sq

remRedund :: Eq b => Gr a b -> Gr a b
remRedund gr = let tc = trc gr
                   redundant (a,b,l) = not $ any (\x -> x /= b && hasEdge (x,b) tc) (suc gr a)
               in  efilter redundant gr

remDupEdges :: Gr a () -> Gr a ()
remDupEdges gr = let f v d [] = d
                     f v d (e:es) | elem e d = f v d es
                                  | elem e v = f v (e:d) es
                                  | otherwise = f (e:v) d es
                     dup = f [] [] (edges gr)
                     ldup = map (\(a,b) -> (a,b,())) dup
                 in  insEdges ldup (delEdges dup gr)

dups :: Array Graph.Vertex CRule -> [(Identifier,Identifier,Maybe Type)] -> Gr Int b -> Node -> [Node]
dups t p gr v | Array.inRange (Array.bounds t) lbl =
                let cr = t Array.! lbl
                    cmp (fld,attr,tp) = getField cr == fld && getAttr cr == attr && sameNT (getType cr) tp
                    sameNT (Just (NT ntA _)) (Just (NT ntB _)) = ntA == ntB
                    sameNT _          _                        = False
                    def = Map.elems (getDefines cr)
                in  case findIndex cmp p of
                      Just _ -> v:concatMap (dups t (def ++ p) gr) succs
                      _      ->   concatMap (dups t (def ++ p) gr) succs
              | otherwise = concatMap (dups t p gr) succs
  where
    (Just lbl) = lab gr v
    succs = suc gr v

remDups :: Array Graph.Vertex CRule -> Node -> Gr Int b -> Gr Int b
remDups t n gr = delNodes (nub $ dups t [] gr n) gr

clean :: Gr a () -> Gr a ()
clean = remRedund . remDupEdges

join :: Gr a () -> TopOrd -> [Node] -> Maybe Node
join tc ts bs = let reachSets = map (suc tc) bs
                    joins | null reachSets = []
                          | otherwise      = foldr1 intersect reachSets
                in  nearestJoin ts joins

nearestGrp :: Gr a b -> Gr a () -> TopOrd -> Node -> [[Node]] -> [Node] -> Maybe SplitJoin
nearestGrp gr tc ts s grp2 xjs = let js  = mapMaybe (\ns -> maybe Nothing (Just . (,) ns) (join tc ts ns)) grp2
                                     js' = filter (flip notElem xjs . snd) js
                                     j    = minimumBy ts (map snd js')
                                     bs   = foldr (union . fst) [] $ filter ((==) j . snd) js'
                                 in  if null js' then Nothing else Just (SJ s (Set.fromList bs) (nodesBetween tc s j) j)

grpBranches :: Gr a b -> Gr a () -> TopOrd -> Node -> [SplitJoin]
grpBranches gr tc ts s = let bs         = suc gr s
                             grp2       = combine bs
                             joins      = mapMaybe (\ns -> maybe Nothing (Just . (,) ns) (join tc ts ns)) grp2
                             cmbGrp (g,j) m = maybe (Map.insert j g m) (\g' -> Map.insert j (g' ++ g) m) (Map.lookup j m)
                             grpMap     = foldr cmbGrp Map.empty joins
                             mkSJ (j,g) = SJ s (Set.fromList g) (nodesBetween tc s j) j
                         in  map mkSJ (Map.assocs grpMap)

splitSplit :: Forest SplitJoin -> ([Node],Gr Int ()) -> ([Node],Gr Int ())
splitSplit [] (sibs,gr)                = (sibs,gr)
splitSplit ((Node sj cs):xs) (sibs,gr) = let split = sjSplit sj
                                             branches = Set.toList (sjBranches sj)
                                             (csN,gr') = splitSplit cs ([],gr)
                                             new = head (newNodes 1 gr')
                                             insNod = insNode (new,-1)
                                             insChildE g = foldr (\c -> insEdge (new,c,())) g csN
                                             insBrsE g = insEdges (map (\b -> (new,b,())) (intersect (suc g split) branches)) g
                                             delBrsE g = delEdges (map ((,) split) branches) g
                                         in  splitSplit xs (new:sibs, delBrsE . insBrsE . insChildE . insNod $ gr') --  

splitJoin :: SplitJoin -> Gr Int () -> Gr Int ()
splitJoin sj gr = let j = sjJoin sj
                      between = sjBetween sj
                      jIn = filter (\(a,_,_) -> elem a between) (inn gr j)
                      new = head (newNodes 1 gr)
                      jIn' = map (\(a,b,_) -> (a,new,())) jIn
                  in  insEdge (new,j,()) . insEdges jIn' . insNode (new,-1) . delEdges (rmELabels jIn) $ gr

splitJoins :: [SplitJoin] -> Gr Int () -> Gr Int ()
splitJoins sjs gr = foldr splitJoin gr sjs

splitSplits :: [SplitJoin] -> Gr Int () -> Gr Int ()
splitSplits [] gr = gr
splitSplits sjs gr = let insSjMap sj m = maybe (Map.insert (sjSplit sj) [sj] m) (\sjs' -> Map.insert (sjSplit sj) (sj:sjs') m) (Map.lookup (sjSplit sj) m)
                         sjMap = foldr insSjMap Map.empty sjs
                         split (s,sjs) gr = let (ns,g) = splitSplit (splitTree sjs) ([],gr)
                                            in  foldr (\n -> insEdge (s,n,())) g ns
                     in  foldr split gr (Map.assocs sjMap)

insSplitTree :: SplitJoin -> Tree SplitJoin -> Tree SplitJoin
insSplitTree sj (Node lab cs) = let bs = sjBranches sj
                                    super = find (Set.isSubsetOf bs . sjBranches . rootLabel) cs
                                    sub = filter (flip Set.isSubsetOf bs . sjBranches . rootLabel) cs
                                    cs' (Just s) = insSplitTree sj s:filter ((/=) s) cs
                                    cs' Nothing  = Node sj sub:filter (flip notElem sub) cs
                                in  Node lab (cs' super)

splitTree :: [SplitJoin] -> Forest SplitJoin
splitTree sjs = let total = foldr (Set.union . sjBranches) Set.empty sjs
                    totalRoot = Node (SJ 0 total [] 0) []
                in  subForest $ foldr insSplitTree totalRoot sjs

linearize1 :: SplitJoin -> Gr a b -> Gr a b
linearize1 sj gr = let betw = sjBetween sj
                       full = (sjSplit sj):(sjJoin sj):betw
                       filtO = filter (\(_,b,_) -> notElem b full)
                       filtI = filter (\(a,_,_) -> notElem a full)
                       o  = concatMap (\n -> filtO (out gr n)) betw
                       i  = concatMap (\n -> filtI (inn gr n)) betw
                       o' = map (\(a,b,l) -> (sjJoin sj,b,l)) o
                       i' = map (\(a,b,l) -> (a,sjSplit sj,l)) i
                   in  (insEdges i' . insEdges o' . delEdges (rmELabels i) . delEdges (rmELabels o)) gr

linearize' :: Eq b => Set Node -> TopOrd -> Gr a b -> Gr a b
linearize' vss ts gr | Set.isSubsetOf splts vss = gr
                     | otherwise                = let s    = Set.findMin (Set.difference splts vss)
                                                      grp2 = combine (suc gr s)
                                                      lin gr xjs = let tc     = trc gr
                                                                       nxt sj = lin (linearize1 sj gr) (sjJoin sj:xjs)
                                                                   in  maybe gr nxt (nearestGrp gr tc ts s grp2 xjs)
                                                  in  linearize' (Set.insert s vss) ts (lin gr [])
  where
    splts = Set.fromList (splits gr)

what :: Show a => a -> a
what x = trace (show x) x

linearize :: Eq b => Gr a b -> Gr a b
linearize gr = let ts = mkTopOrd gr
               in  (linearize' Set.empty ts) gr

sjs' :: Gr a b -> [SplitJoin]
sjs' gr = let tc = trc gr
              ts = mkTopOrd gr
          in  concatMap (grpBranches gr tc ts) (splits gr)

sortSj :: (SplitJoin -> Node) -> TopOrd -> [SplitJoin] -> [SplitJoin]
sortSj f ts = sortBy (\a b -> ts (f a) (f b))

sortBySplit :: TopOrd -> [SplitJoin] -> [SplitJoin]
sortBySplit = sortSj sjSplit

treeize1 :: SplitJoin -> Gr a EdgeType -> Gr a EdgeType
treeize1 sj gr = let detJoin = delEdges (rmELabels (inn gr $ sjJoin sj))
                     attJoin = insEdge (sjSplit sj,sjJoin sj,Seq)
                 in  (attJoin . detJoin) gr

treeize :: [SplitJoin] -> Gr a b -> Gr a EdgeType
treeize sjs gr = foldr treeize1 (labelEdges gr) sjs

labelEdges :: Gr a b -> Gr a EdgeType
labelEdges gr = emap (const Par) gr

splitTaskGraph :: Gr Int () -> Gr Int ()
splitTaskGraph tg = let sjs = sjs' tg
                    in  splitJoins sjs . splitSplits sjs $ tg

taskTree :: Gr a () -> Gr a EdgeType
taskTree stg = treeize (sjs' stg) stg

mkParTree :: Set Node -> PSTree -> ParTree Node
mkParTree sq tt = let src = sources tt
                      bld n = let (p,s) = partition ((==) Par . snd) (lsuc tt n)
                                  (sp,pp) = partition (flip Set.member sq . fst) p
                                  p' = map (bld . fst) pp
                                  s' = map (bld . fst) (sp ++ s)
                                  (Just v) = lab tt n
                              in  case ((length p',length s')) of
                                    (0,0) -> TSingle v
                                    (1,0) -> TSeq (TSingle v) (head p')
                                    (0,_) -> TSeq (TSingle v) (foldr1 TSeq s')
                                    (1,_) -> TSeq (TSingle v) (foldr1 TSeq (p' ++ s'))
                                    (_,0) -> TSeq (TSingle v) (foldr1 TPar p')
                                    (_,_) -> TSeq (TSingle v) $ TSeq (foldr1 TPar p') (foldr1 TSeq s')
                  in  if null src then TNone else bld (head src)

remTempNodes :: ParTree Node -> ParTree Node
remTempNodes = filterParTree ((<) 0)

filterParTree :: (a -> Bool) -> ParTree a -> ParTree a
filterParTree f (TPar (TSingle x) b) | not (f x) = filterParTree f b
filterParTree f (TPar a (TSingle x)) | not (f x) = filterParTree f a
filterParTree f (TPar a b) = TPar (filterParTree f a) (filterParTree f b)
filterParTree f (TSeq (TSingle x) b) | not (f x) = filterParTree f b
filterParTree f (TSeq a (TSingle x)) | not (f x) = filterParTree f a
filterParTree f (TSeq a b) = TSeq (filterParTree f a) (filterParTree f b)
filterParTree f (TSingle x) | not (f x) = TNone
                            | otherwise = TSingle x
filterParTree f TNone = TNone

cleanParTree' :: Eq a => ParTree a -> ParTree a
cleanParTree' (TPar TNone b) = cleanParTree b
cleanParTree' (TPar a TNone) = cleanParTree a
cleanParTree' (TPar a b) = TPar (cleanParTree a) (cleanParTree b)
cleanParTree' (TSeq TNone b) = cleanParTree b
cleanParTree' (TSeq a TNone) = cleanParTree a
cleanParTree' (TSeq a b) = TSeq (cleanParTree a) (cleanParTree b)
cleanParTree' x = x

cleanParTree :: Eq a => ParTree a -> ParTree a
cleanParTree x = let y = cleanParTree' x
                 in  if x == y then x else cleanParTree y

instance Functor ParTree where
  fmap f = foldParTree (TPar,TSeq,TSingle . f,TNone)

flattenParTree :: ParTree a -> [a]
flattenParTree = foldParTree ((++),(++),flip (:) [],[])

foldParTree :: (r -> r -> r,r -> r -> r,a -> r,r) -> ParTree a -> r
foldParTree (p,q,s,n) (TPar a b) = p (foldParTree (p,q,s,n) a) (foldParTree (p,q,s,n) b)
foldParTree (p,q,s,n) (TSeq a b) = q (foldParTree (p,q,s,n) a) (foldParTree (p,q,s,n) b)
foldParTree (p,q,s,n) (TSingle a) = s a
foldParTree (p,q,s,n) (TNone) = n
