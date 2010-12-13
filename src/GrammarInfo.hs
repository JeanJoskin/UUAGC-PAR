module GrammarInfo where

import SequentialTypes
import CodeSyntax
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import CommonTypes
import Data.List(intersect,(\\))
import Control.DeepSeq
import Patterns (Pattern (..))

type LMH = (Vertex,Vertex,Vertex)
data Info = Info  {  tdpToTds    ::  Table Vertex
                  ,  tdsToTdp    ::  Table [Vertex]
                  ,  attrTable   ::  Table NTAttr
                  ,  ruleTable   ::  Table CRule
                  ,  lmh         ::  [LMH]
                  ,  nonts       ::  [(NontermIdent,[ConstructorIdent])]
                  ,  wraps       ::  Set NontermIdent
                  }
                  deriving Show

instance NFData Info where
  rnf info = tdpToTds info `deepseq` tdsToTdp info `deepseq` attrTable info `deepseq` ruleTable info `deepseq`
             lmh info `deepseq` nonts info `deepseq` wraps info `seq` ()

instance NFData CRule where
  rnf (CRule nm isIn hc nt con fld cnt tp pat rhs def owrt ori use expl mbn hvy) =
    nm `deepseq` isIn `deepseq` hc `deepseq` nt `deepseq` con `deepseq` fld `deepseq` cnt `deepseq` tp `deepseq` rhs `deepseq` def `deepseq` owrt `deepseq` use `deepseq` expl `deepseq` mbn `deepseq` hvy `deepseq` ()
  rnf (CChildVisit nm nt nr inh syn isl parc) =
    nm `deepseq` nt `deepseq` nr `deepseq` inh `deepseq` syn `deepseq` isl `deepseq` parc `deepseq` ()

instance Show CRule
 where show (CRule name isIn hasCode nt con field childnt tp pattern rhs defines owrt origin uses _ _ _) 
         = "CRule " ++ show name ++ " nt: " ++ show nt ++ " con: " ++ show con ++ " field: " ++ show field
         ++ " childnt: " ++ show childnt ++ " rhs: " ++ concat rhs ++ " uses: " ++ show [ attrname True fld nm | (fld,nm) <- Set.toList uses ]

instance NFData Pattern where
  rnf (Constr n ps) = n `deepseq` ps `deepseq` ()
  rnf (Product pos pats) = pos `seq` pats `deepseq` ()
  rnf (Alias fld attr pat parts) = fld `deepseq` attr `deepseq` pat `deepseq` parts `deepseq` ()
  rnf (Irrefutable pat) = pat `deepseq` ()
  rnf (Underscore p) = p `seq` ()

type CInterfaceMap = Map NontermIdent CInterface
type CVisitsMap = Map NontermIdent (Map ConstructorIdent CVisits)

data CycleStatus  
  = CycleFree     CInterfaceMap CVisitsMap [(String,String)]
  | LocalCycle    [Route] [(String,String)]
  | InstCycle     [Route] [(String,String)]
  | DirectCycle   [EdgeRoutes] [(String,String)]
  | InducedCycle  CInterfaceMap [EdgeRoutes] [(String,String)]

showsSegment :: CSegment -> [String]
showsSegment (CSegment inh syn)
   = let syn'     = map toString (Map.toList syn)
         inh'     = map toString (Map.toList inh)
         toString (a,t) = (getName a, case t of (NT nt tps) -> getName nt ++ " " ++ unwords tps; Haskell t -> t)
         chnn     = inh' `intersect` syn'
         inhn     = inh' \\ chnn
         synn     = syn' \\ chnn
         disp name [] = []
         disp name as =  (name ++ if length as == 1 then " attribute:" else " attributes:") :
                         map (\(x,y) -> ind x ++ replicate ((20 - length x) `max` 0) ' ' ++ " : " ++ y) as
     in  disp "inherited" inhn 
         ++ disp "chained" chnn
         ++ disp "synthesized" synn

