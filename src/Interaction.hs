{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
module Interaction where

import Data.Graph.Inductive
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.NodeMap
import Data.Maybe (fromJust)

data PortType = Prim
              | Aux1
              | Aux2
              | Aux3
              | Aux4
              | Aux5
              deriving (Ord,Eq, Show)

data NumPort = Port PortType Node
             | FreePort
             deriving Show

data EdgeInfo = Edge (Node, PortType) (Node, PortType) deriving Show

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

-- Rewrite REL into tagless final, so we aren't wasting memory on this silly tag, just pass in the function!
-- | REL, a type that displays whether or not we are relinking from an old node or just adding a new link
data REL a = Link a
           | ReLink Node PortType
           deriving (Show)

-- | Type for specifying how one wants to link nodes
data Relink
  = RELAuxiliary2 { node :: Node, primary :: REL NumPort, auxiliary1 :: REL NumPort, auxiliary2 :: REL NumPort }
  | RELAuxiliary1 { node :: Node, primary :: REL NumPort, auxiliary1 :: REL NumPort }
  | RELAuxiliary0 { node :: Node, primary :: REL NumPort }
  deriving (Show)

-- invariant, nodes must be connected to each other, thus un-directed
type Net = Gr Lang EdgeInfo

-- Graph to more typed construction-------------------------------------------------------
aux0FromGraph :: (Primary -> ProperPort) -> Net -> Node -> Maybe ProperPort
aux0FromGraph constructor graph num =
  foldr f (constructor Free) . lneighbors' <$> fst (match num graph)
  where
    f (Edge (n1, n1port) (n2, n2port), n) con
      | n1 == num && Prim == n1port = con {prim = Primary n2}
      | n2 == num && Prim == n2port = con {prim = Primary n1}
    f _ con = con

aux2FromGraph ::
     (Primary -> Auxiliary -> Auxiliary -> ProperPort)
  -> Net
  -> Node
  -> Maybe ProperPort
aux2FromGraph constructor graph num =
  foldr f (constructor Free FreeNode FreeNode) . lneighbors' <$> fst (match num graph)
  where
    f (Edge (n1, n1port) (n2, n2port), n) con
      | n1 == num = conv (n2, n1port) con
      | n2 == num = conv (n1, n2port) con
      | otherwise = con
    conv (n,Prim) con = con {prim = Primary n}
    conv (n,Aux1) con = con {aux1 = Auxiliary n}
    conv (n,Aux2) con = con {aux2 = Auxiliary n}
    conv (n,_) con = con

conFromGraph :: Net -> Node -> Maybe ProperPort
conFromGraph = aux2FromGraph Construct

dupFromGraph :: Net -> Node -> Maybe ProperPort
dupFromGraph = aux2FromGraph Duplicate

eraFromGraph :: Net -> Node -> Maybe ProperPort
eraFromGraph = aux0FromGraph Erase

-- a bit of extra repeat work in this function!
langToProperPort :: Net -> Node -> Maybe ProperPort
langToProperPort graph n = do
  context <- fst (match n graph)
  case snd (labNode' context) of
    Con -> conFromGraph graph n
    Dup -> dupFromGraph graph n
    Era -> eraFromGraph graph n

-- Graph manipulation ----------------------------------------------------------

reduce :: Net -> Maybe Net
reduce net =
  let (newNet, isChanged) = foldr update (net,False) netNodes in
    if isChanged then Just newNet else Nothing
  where
    netNodes = nodes net
    update n (net, isChanged) =
      case langToProperPort net n of
        Nothing   -> (net, isChanged)
        Just port ->
          -- The main port we are looking at
          case port of
            Construct Free _ _                 -> (net, isChanged)
            con@(Construct (Primary node) _ _) ->
              case langToProperPort net node of
                Nothing               -> error "nodes are undirected, precondition violated!"
                Just d@(Duplicate {}) -> (conDup net n node con d, True)
                Just (Erase {})       -> (erase net n node con, True)
                Just c@(Construct {}) -> (annihilate net n node con c, True)
            (Duplicate Free _ _)               -> (net, isChanged)
            dup@(Duplicate (Primary node) _ _) ->
              case langToProperPort net node of
                Nothing -> error "nodes are undirected, precondition violated!"
                Just d@(Duplicate {}) -> (annihilate net n node dup d, True)
                Just (Erase {})       -> (erase net n node dup, True)
                Just c@(Construct {}) ->  (conDup net node n c dup, True)
            (Erase Free)           -> (net, isChanged)
            (Erase (Primary node)) ->
              case langToProperPort net node of
                Nothing -> (net, isChanged)
                Just x   -> (erase net node n x, True)

-- | Deals with the case when two nodes annihilate each other
annihilate :: Net -> Node -> Node -> ProperPort -> ProperPort -> Net
annihilate net conNum1 conNum2 (Construct _ auxA auxB) (Construct _ auxC auxD)
  = delNodes [conNum1, conNum2]
  $ rewire (rewire net (Aux1, auxA) (Aux2, auxD)) (Aux2, auxB) (Aux1, auxC)

annihilate net conNum1 conNum2 (Duplicate _ auxA auxB) (Duplicate _ auxC auxD)
  = delNodes [conNum1, conNum2]
  $ rewire (rewire net (Aux1, auxA) (Aux1, auxC)) (Aux2, auxB) (Aux2, auxD)
annihilate _ _ _ _ _ = error "the other nodes do not annihilate eachother"

-- | Deals with the case when an Erase Node hits any other node
erase :: Net -> Node -> Node -> ProperPort -> Net
erase net conNum eraseNum port
  = case port of
      (Construct {}) -> delNodes [conNum, eraseNum] (foldr (flip linkAll) net'' [nodeA, nodeB])
      (Duplicate {}) -> delNodes [conNum, eraseNum] (foldr (flip linkAll) net'' [nodeA, nodeB])
      (Erase {})     -> delNodes [conNum, eraseNum] net
  where
    (eraA, net')  = newNode net Era
    (eraB, net'') = newNode net' Era
    nodeA         = RELAuxiliary0 { node = eraA, primary = ReLink conNum Aux1 }
    nodeB         = RELAuxiliary0 { node = eraB, primary = ReLink conNum Aux2 }

-- | conDup deals with the case when Constructor and Duplicate share a primary
conDup :: Net -> Node -> Node -> ProperPort -> ProperPort -> Net
conDup net conNum deconNum (Construct _ auxA auxB) (Duplicate _ auxC auxD)
  = delNodes [conNum, deconNum]
  $ foldr (flip linkAll)
          net''''
          [nodeA, nodeB, nodeC, nodeD]
  where
    (dupA, net')    = newNode net    Dup
    (dupB, net'')   = newNode net'   Dup
    (conC, net''')  = newNode net''  Con
    (conD, net'''') = newNode net''' Con
    nodeA = RELAuxiliary2 { node       = dupA
                          , primary    = ReLink conNum Aux1
                          , auxiliary1 = Link (Port Aux1 conC)
                          , auxiliary2 = Link (Port Aux1 conD)
                          }
    nodeB = RELAuxiliary2 { node       = dupB
                          , primary    = ReLink conNum Aux2
                          , auxiliary1 = Link (Port Aux2 conC)
                          , auxiliary2 = Link (Port Aux2 conD)
                          }
    nodeC = RELAuxiliary2 { node       = conC
                          , primary    = ReLink deconNum Aux1
                          , auxiliary1 = Link (Port Aux1 dupA)
                          , auxiliary2 = Link (Port Aux1 dupB)
                          }
    nodeD = RELAuxiliary2 { node       = conD
                          , primary    = ReLink deconNum Aux2
                          , auxiliary1 = Link (Port Aux2 dupA)
                          , auxiliary2 = Link (Port Aux2 dupB)
                          }
conDup _ _ _ _ _ = error "only send a construct and duplicate to conDup"
-- Manipulation functions ------------------------------------------------------

linkHelper net rel nodeType node =
  case rel of
    Link (Port portType node1) -> link net (node, nodeType) (node1, portType)
    Link FreePort              -> net
    ReLink oldNode oldPort     -> relink net (oldNode, oldPort) (node, nodeType)


linkAll :: Net -> Relink -> Net
linkAll net (RELAuxiliary0 {primary, node}) =
  linkHelper net primary Prim node
linkAll net (RELAuxiliary1 {primary, node, auxiliary1}) =
  linkHelper (linkHelper net primary Prim node) auxiliary1 Aux1 node
linkAll net (RELAuxiliary2 {primary, node, auxiliary1, auxiliary2}) =
  foldr (\ (typ,nodeType) net -> linkHelper net typ nodeType node)
        net
        [(primary, Prim), (auxiliary1, Aux1), (auxiliary2, Aux2)]


link :: Net -> (Node, PortType) -> (Node, PortType) -> Net
link net (node1, port1) (node2, port2) =
  insEdge (node1, node2, Edge (node1, port1) (node2, port2)) net

-- post condition, must delete the old node passed after the set of transitions are done!
relink :: Net -> (Node, PortType) -> (Node, PortType) -> Net
relink net (oldNode, port) new@(newNode, newPort) =
  case findEdge net oldNode port of
    Just relink@(nodeToRelink, _) ->
      insEdge (nodeToRelink, newNode, Edge relink new) net
    -- The port was really free to begin with!
    Nothing -> net

-- | rewire is used to wire two auxiliary nodes together
-- when the main nodes annihilate each other
rewire :: Net -> (PortType, Auxiliary) -> (PortType, Auxiliary) -> Net
rewire net (pa, (Auxiliary a)) (pb, (Auxiliary b)) = link net (a, pa) (b, pb)
rewire net _ _                                     = net

newNode :: DynGraph gr => gr a b -> a -> (Node, gr a b)
newNode graph lang = (succ maxNum, insNode (succ maxNum, lang) graph)
  where
    (_,maxNum) = nodeRange graph

auxToPrimary (Auxiliary node) = Primary node
auxToPrimary FreeNode         = Free

shead (x:_) = Just x
shead []    = Nothing

-- Precond, node must exist in the net with the respective port
findEdge :: Net -> Node -> PortType -> Maybe (Node, PortType)
findEdge net node port
  = fmap other
  $ shead
  $ filter f
  $ lneighbors net node
  where
    f (Edge t1 t2, n)
      | t1 == (node, port) = True
      | t2 == (node, port) = True
      | otherwise          = False
    other (Edge t1 t2, n)
      | t1 == (node, port) = t2
      | t2 == (node, port) = t1
      | otherwise          = error "doesn't happen"
-- Example Graphs --------------------------------------------------------------

exampleNet :: Net
exampleNet = buildGr
             [( [ (Edge (2, Prim) (1, Prim), 2) ], 1, Con, [])
             ,([], 2, Dup, [])
             ]
