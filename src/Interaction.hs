{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Interaction where


import Data.Graph.Inductive
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.NodeMap


data PortType = Prim
              | Aux1
              | Aux2
              | Aux3
              | Aux4
              | Aux5
              deriving (Ord,Eq, Show)

-- Eventually turn this into a GADΤ with more info?
data Lang where
  Con :: Lang
  Dup :: Lang
  Era :: Lang

deriving instance Show Lang

-- Leave these as GADTs for now!
data Primary where
  Primary :: Node -> Primary
  Free    :: Primary

deriving instance Show Primary

data Auxiliary = Auxiliary Node
               | FreeNode
               deriving Show
-- eventually turn this into a nice Class representation to easily extend!
data ProperPort
  = Construct {prim :: Primary, aux1 :: Auxiliary, aux2 :: Auxiliary}
  | Duplicate {prim :: Primary, aux1 :: Auxiliary, aux2 :: Auxiliary}
  | Erase     {prim :: Primary}
  deriving (Show)

-- Graph to more typed construction-------------------------------------------------------
aux0FromGraph :: Graph gr => (Primary -> ProperPort) -> gr a PortType -> Node -> Maybe ProperPort
aux0FromGraph constructor graph num =
  foldr f (constructor Free) . lsuc' <$> fst (match num graph)
  where
    nodes          = lsuc graph num
    f (n,Prim) con = con {prim = Primary n}
    f (_,_)    con = con

aux2FromGraph :: Graph gr
  => (Primary -> Auxiliary -> Auxiliary -> ProperPort)
  -> gr a PortType
  -> Node
  -> Maybe ProperPort
aux2FromGraph constructor graph num =
  foldr f (constructor Free FreeNode FreeNode) . lsuc' <$> fst (match num graph)
  where
    f (n,Prim) con = con {prim = Primary n}
    f (n,Aux1) con = con {aux1 = Auxiliary n}
    f (n,Aux2) con = con {aux2 = Auxiliary n}
    f (n,_) con = con


conFromGraph :: Graph gr => gr a PortType -> Node -> Maybe ProperPort
conFromGraph = aux2FromGraph Construct

dupFromGraph :: Graph gr => gr a PortType -> Node -> Maybe ProperPort
dupFromGraph = aux2FromGraph Duplicate

eraFromGraph :: Graph gr => gr a PortType -> Node -> Maybe ProperPort
eraFromGraph = aux0FromGraph Erase

-- a bit of extra repeat work in this function!
langToProperPort :: Graph gr => gr Lang PortType -> Node -> Maybe ProperPort
langToProperPort graph n = do
  context <- fst (match n graph)
  case snd (labNode' context) of
    Con -> conFromGraph graph n
    Dup -> dupFromGraph graph n
    Era -> eraFromGraph graph n

-- Graph manipulation ----------------------------------------------------------

reduce :: Net -> Maybe Net
reduce net = undefined
  where
    netNodes = nodes net
    recursive graph (n:ns) isChanged =
      case langToProperPort graph n of
        Nothing   -> recursive graph ns isChanged
        Just port ->
          -- The main port we are looking at
          case port of
            Construct Free _ _                 -> recursive graph ns isChanged
            Construct (Primary node) aux1 aux2 ->
              case langToProperPort graph node of
                Nothing -> error "nodes are undirected, precondition violated!"
                Just port ->
                  undefined
    recursive graph [] True  = Just graph
    recursive graph [] False = Nothing
-- Manipulation functions ------------------------------------------------------

newNode :: DynGraph gr => gr a b -> a -> gr a b
newNode graph lang = insNode (succ maxNum, lang) graph
  where
    (_,maxNum) = nodeRange graph

-- Example Graphs --------------------------------------------------------------

-- invariant, nodes must be connected to each other, thus un-directed
type Net = Gr Lang PortType

exampleNet :: Net
exampleNet = buildGr
             [([(Prim, 2)], 1, Con, [(Prim, 2)])
             ,([], 2, Dup, [])
             ]
