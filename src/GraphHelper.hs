{-# LANGUAGE FlexibleInstances #-}
module GraphHelper where

import qualified Data.Graph.Inductive.PatriciaTree as G
import qualified Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.Query.SP
import qualified Data.Map.Strict as M
import qualified Data.Maybe as Mb
import qualified Data.List as L
import qualified Data.Set as S
import Data.Function (on)
import Data.Tuple (swap)

nodesToPath ns = zip (init ns) (tail ns)

data Tree a = Tree a [Tree a]
  deriving (Show, Read)

type ChildMap a = M.Map a (S.Set a)
type PathMap a = M.Map a [a]

type Edge a = S.Set a   -- 2 elements only!

instance Ord a => Eq (Tree a) where
  t1 == t2 = toChildMap t1 == toChildMap t2

root :: Tree a -> a
root (Tree r _) = r

size :: Tree a -> Int
size (Tree _ []) = 1
size (Tree _ ts) = 1 + sum (map size ts)

elements :: Tree a -> [a]
elements (Tree x ts) = x: concatMap elements ts

toChildMap :: Ord a => Tree a -> ChildMap a
toChildMap (Tree r []) = M.singleton r S.empty
toChildMap (Tree r ts) = M.unions $ M.singleton r (S.fromList $ map root ts): map toChildMap ts


toTree :: Ord a => a -> ChildMap a -> Tree a
toTree r cm =
  let ps = M.keys $ M.filter (r `S.member`) cm
      cm' = foldl (flip $ M.adjust (S.delete r)) cm ps
  in Tree r $ map ( `toTree` cm') ps
      ++ map (\c -> toTree c (M.delete r cm))  (S.toList $ cm M.! r)

rootChildMap :: Ord a => ChildMap a -> a
rootChildMap cm =
  let [k] = filter (\n -> not $ S.member n $ S.unions $ M.elems cm) $ M.keys cm
  in k

removeLeave :: Ord a => a -> ChildMap a -> ChildMap a
removeLeave l cm =
  if null $ cm M.! l
    then M.map (S.delete l ) $ M.delete l cm
    else error "don't remove non leaves!"

subTreeAt :: Eq a => Tree a -> a -> Maybe (Tree a)
subTreeAt t@(Tree r ts) u = if r == u
  then Just t
  else Mb.listToMaybe $ Mb.mapMaybe (`subTreeAt` u) ts

parent :: Ord a => ChildMap a -> a -> a
parent cm v =
  let [p] = M.keys $ M.filter (S.member v) cm
  in p

-- kanten gerichtet: down
edges :: Ord a => ChildMap a -> [Edge a]
edges = M.foldrWithKey (\r cs es -> map (\c -> S.fromList [r,c]) (S.toList cs)  ++ es) []

undirect :: Ord a => (a,a) -> Edge a
undirect (u,v) = S.fromList [min u v, max u v]
--
-- normalize :: Ord a => Edge a -> Edge a
-- normalize (Edge u v) = Edge (min u v) (max u v)

member :: Ord a => a -> Edge a -> Bool
member = S.member
--
-- toSet :: Ord a => Edge a -> S.Set a
-- toSet (Edge u v) = S.fromList [u,v]
--
-- fromSet :: S.Set a -> Edge a
-- fromSet s =
--   let [u,v] = S.toList s
--   in Edge u v

rootPaths :: Ord a => Tree a -> PathMap a
rootPaths (Tree r []) = M.singleton r [r]
rootPaths (Tree r ts) = M.unions $ M.singleton r [r] :
  ( M.map (r:) . rootPaths <$> ts)

path :: Ord a => PathMap a -> a -> a -> [(a,a)]
path p u v =
  let (upath, vpath) = applyToBoth nodesToPath $ pathsToLca p u v
  in upath ++ vpath

longestCommonPrefix :: Eq a => [a] -> [a] -> [a]
longestCommonPrefix _ [] = []
longestCommonPrefix [] _ = []
longestCommonPrefix (x:xs) (y:ys) =
  if x == y
    then x: longestCommonPrefix xs ys
    else []

lca :: Ord a => PathMap a -> a -> a -> a
lca tm u v = last $ longestCommonPrefix (tm M.! u) (tm M.! v)

applyToBoth :: (a -> b) -> (a,a) -> (b,b)
applyToBoth f (x,y) = (f x, f y)

pathsToLca :: Ord a => PathMap a -> a -> a -> ([a],[a])
pathsToLca pm u v = applyToBoth
  (\x -> dropWhile (lca pm u v /=) $ pm M.! x) (u,v)

-- richtung: down
dirOfEdge :: Ord a => ChildMap a -> Edge a -> (a,a)
dirOfEdge cm e =
  let [u,v] = S.toList e
  in if v `S.member` (cm M.! u)
      then (u,v)
      else (v,u)

-- kante gerichtet: down
congestion :: Ord a => Tree a -> Edge a -> Int
congestion t e =
  let cm = toChildMap t
  in if e `elem` edges cm
      then let (u,v) = dirOfEdge cm e in size $ Mb.fromJust $ subTreeAt t v
      else 0

edgesInUnion :: Ord a => Tree a -> Tree a -> [Edge a]
edgesInUnion t1 t2 =
  let (cm1, cm2) = applyToBoth (edges . toChildMap) (t1,t2)
  in L.union cm1 cm2

neighbors :: Ord a => a -> S.Set (Edge a) -> S.Set a
neighbors v es = S.map
  (\e -> let [x,y] = S.toList e in if x == v then y else x)
  $ S.filter (member v) es

fromEdges :: Ord a => a -> S.Set (Edge a) -> ChildMap a
fromEdges r es =
  let rns = neighbors r es
  in M.unions $ M.singleton r rns:
      map (\v -> fromEdges v $ S.filter (not . member r) es ) (S.toList rns)

nodes :: Ord a => S.Set (Edge a) -> S.Set a
nodes = S.unions

leaves :: ChildMap a -> [a]
leaves cm = M.keys $ M.filter null cm

edgesOfComplete :: Int -> [Edge Int]
edgesOfComplete n = concatMap (\i -> [S.fromList[i,j] | j <- [i+1 .. n]]) [1 .. n]

canonicalSpanningTreeOfComplete :: Int -> [Edge Int]
canonicalSpanningTreeOfComplete n = [ S.fromList[i,i+1] | i <- [1 .. n-1]]

gridcols w h = [S.fromList [(x,y), (x, y-1)] | x <- [1 .. w], y <- [2 .. h]]

edgesOfGrid :: Int -> Int -> [Edge (Int,Int)]
edgesOfGrid w h = let
  rows = [S.fromList [(x,y), (x-1, y)] | x <- [2 .. w], y <- [1 .. h]]
  in  gridcols w h ++ rows

canonicalSpanningTreeOfGrid :: Int -> Int -> [Edge (Int,Int)]
canonicalSpanningTreeOfGrid w h = let
  row = [S.fromList [(x,1), (x-1, 1)] | x <- [2 .. w]]
  in  gridcols w h ++ row

pathFromPerm [x] = Tree x []
pathFromPerm (x:xs) = Tree x [pathFromPerm xs]



edgesOfWheel n = [S.fromList [0,i] | i <- [1 .. n]] ++ [S.fromList [i,i+1] | i <- [1 .. n-1]] ++ [S.fromList [n,1]]
canonicalSpanningTreeOfWheel n = [S.fromList [0,i] | i <- [1 .. n]]

edgesOfHypercube 1 = [S.fromList [[0],[1]]]
edgesOfHypercube d =
  let es = edgesOfHypercube $ d-1
      ns = S.toList $ nodes $ S.fromList es
  in concatMap ((\[u,v] -> [ S.fromList [0:u, 0:v], S.fromList [1:u, 1:v]]) . S.toList) es
    ++ map (\u -> S.fromList [0:u, 1:u]) ns

canonicalSpanningTreeOfHypercube 1 = [S.fromList [[0],[1]]]
canonicalSpanningTreeOfHypercube d =
  let st = canonicalSpanningTreeOfHypercube $ d-1
  in concatMap ((\[u,v] -> [ S.fromList [0:u, 0:v], S.fromList [1:u, 1:v]]) . S.toList) st
     ++ [S.fromList [ replicate d 0, 1: replicate (d-1) 0 ]]


edgesOfFan n = canonicalSpanningTreeOfFan n ++ [S.fromList [i,i+1] | i <- [1 .. n-1]]
canonicalSpanningTreeOfFan n = [S.fromList [0,i] | i <- [1 .. n]]

edgesOfFanOfFans n k =
  let fes = edgesOfFan n
  in [S.fromList [[0], [i,0]] | i <- [1 .. k]] ++ [S.fromList [[i,0], [i+1,0]] | i <- [1 .. k-1]]
    ++ concatMap ((\[u,v] -> [S.fromList [[i,u], [i,v]] | i <- [1 .. k] ]) . S.toList) fes

canonicalSpanningTreeOfFanOfFans n k =
  let st = canonicalSpanningTreeOfFan n
  in [S.fromList [[0], [i,0]] | i <- [1 .. k]] ++
     concatMap ((\[u,v] -> [S.fromList [[i,u], [i,v]] | i <- [1 .. k] ]) . S.toList) st


-- find all spanning trees
hasPath :: Ord a => a -> a -> S.Set (Edge a) -> Bool
hasPath u v _ | u == v = True
hasPath u v es =
  not (S.null es || not (v `S.member` nodes es))
  && (let uns = neighbors u es
          ues = S.filter (member u) es
      in (v `S.member` uns) || any (\n -> hasPath n v $ es S.\\ ues) uns
     )

containsCycle :: Ord a => S.Set (Edge a) -> Bool
containsCycle es = any
  (\e -> let [u,v] = S.toList e in hasPath u v (S.delete e es))
  $ S.toList es


-- find all spanning trees by alg S in AOCP 4A
-- achtung: nearst MUSS nearst in es sein ((n-2) Kanten, ohne Kreis)

contract :: Ord a => M.Map Int (Edge a) -> (Int, Edge a) -> M.Map Int (Edge a)
contract em (l, e) =
  let [u,v] = S.toList e
  in M.map S.fromList
      $ M.filter
      (\xs -> length xs /= 1)
      $ M.map
            (\e' ->
                let nes' = if v `S.member` e'
                            then S.insert u (S.delete v e')
                            else e'
                in S.toList nes'
            )
            $ M.delete l em

isBridge :: Ord a => M.Map Int (Edge a) -> Int -> Bool
isBridge em l =
  let [u,v]= S.toList $ em M.! l
  in not $ hasPath u v $ S.fromList $ M.elems $ M.delete l em

allSpanningTreesAt' :: Ord a => S.Set a -> M.Map Int (Edge a) -> M.Map Int (Edge a) -> [Int] -> [[Int]]
allSpanningTreesAt' ns origem currem nearst =
  if S.size ns == 2 || null nearst
    then map (:[]) $ M.keys currem
    else
      let l = head nearst
          stscontract = allSpanningTreesAt' ns origem (contract currem (l, currem M.! l)) (tail nearst)
          stsdelete = if isBridge currem l
            then []
            else allSpanningTreesAt' ns origem (M.delete l currem) (last stscontract)
      in map (l:) stscontract ++ stsdelete

allSpanningTreesAt :: Ord a => a -> [Edge a] -> [Edge a] -> [ChildMap a]
allSpanningTreesAt r es nearst =
  let ns = nodes $ S.fromList es
      em = M.fromList $ zip [1 ..] es
      me = M.fromList $ zip es [1 .. ]
      lnearst = map (me M.!) nearst
  in map (fromEdges r . S.fromList . map (em M.!)) $ allSpanningTreesAt' ns em em lnearst

-- tree isomorphism check Aho, Hopcroft, Ullman
assignCanonicalNameToRoot :: Tree a -> String
assignCanonicalNameToRoot (Tree r []) = "01"
assignCanonicalNameToRoot (Tree r cs) =
  let cnames = L.sort $ map assignCanonicalNameToRoot cs
  in unwords (("0" : cnames) ++ ["1"])

isomorph :: Tree a -> Tree a -> Bool
isomorph t1 t2 =
  let (nr1, nr2) = applyToBoth assignCanonicalNameToRoot (t1,t2)
  in nr1 == nr2

treeDisjoint :: Ord a => ChildMap a -> ChildMap a -> Bool
treeDisjoint t1 t2 = uncurry S.disjoint $ applyToBoth ( S.fromList . edges) (t1,t2)


binaryTreeOfHeight :: Int -> Tree Int
binaryTreeOfHeight h =
  let binaryTreeAt r 0 = Tree r []
      binaryTreeAt r h' = Tree r [binaryTreeAt (2*r) (h'-1), binaryTreeAt (2*r + 1) (h'-1)]
  in binaryTreeAt 1 h


levelOfBinary :: Int -> [Int]
levelOfBinary l = [2^l .. (2^(l+1) -1)]



type WeightedEdges a b = M.Map (S.Set a) b

nodesOf :: Ord a => WeightedEdges a b -> S.Set a
nodesOf es = S.unions $ M.keys es

optTreeAt :: (Ord a, Ord b) => a -> WeightedEdges a b -> ChildMap a
optTreeAt r em =
  let extendOpt es em' =
        let newem = M.filterWithKey
                      (\e _ -> not $ containsCycle $ S.fromList $ e:es)
                      em'
            e = fst $ L.minimumBy (compare `on` snd) $ M.toList newem
        in if null newem
            then es
            else extendOpt (e:es) (M.delete e newem)
  in fromEdges r $ S.fromList $ extendOpt [] em

isNEin :: (Ord a, Ord b, Fractional b) => WeightedEdges a b -> ChildMap a -> Bool
isNEin em tcm =
  let extes = M.keys $ M.withoutKeys em (S.fromList $ edges tcm)
      neconds e =
        let t = toTree (rootChildMap tcm) tcm
            [u,v] = S.toList e
            (upath, vpath) = applyToBoth (map undirect . nodesToPath)
                              $ pathsToLca (rootPaths t) u v
            sumWeights p = sum $ (\pe -> (em M.! pe) / fromIntegral (congestion t pe)) <$> p
            sumWeights' p = sum $ (\pe -> (em M.! pe) / fromIntegral (1 + congestion t pe)) <$> p
            necond p1 p2 = em M.! e + sumWeights' p1 >= sumWeights p2
        in necond upath vpath && necond vpath upath
  in all neconds extes

soccost :: (Num b, Ord a) => WeightedEdges a b -> S.Set (S.Set a) -> b
soccost em es = sum $ M.elems $ M.restrictKeys em es

-- soccost l xs t =
--  linearComb $ map (\e -> (xs M.! e, l (congestion t e))) $ edges $ toChildMap t

soccost' :: (Ord a) => (Int -> Rational) -> Tree a -> M.Map (Edge a) Rational -> Rational
soccost' l t em = sum $ (\e -> l (congestion t e)* (em M.! e) ) <$> edges (toChildMap t)

data Res a b = POSRes { ratio :: !b, opt :: ![Edge a], bestne :: ![Edge a] }
  | GNENERes { gap :: !b, bestne :: ![Edge a], bestgne :: ![Edge a] }
  deriving Show

pos :: (Node a, Ord a, Ord b, Fractional b) => a -> WeightedEdges a b -> Res a b
pos r em =
  let opt = edges $ optTreeAt r em
      h = S.fromList
      nes = filter (isNEin em)
              $ allSpanningTreesAt r (M.keys em) (init opt)
      best = L.minimumBy (compare `on` soccost em . h)
            $ edges <$> nes
  in POSRes{ratio = soccost em (h best) / soccost em (h opt), opt = opt, bestne = best}

gnenegap :: (Ord a, Fractional b, Real b, Ord b) => a -> WeightedEdges a b -> Res a b
gnenegap r em =
  let opt = edges $ optTreeAt r em
      sts = allSpanningTreesAt r (M.keys em) (init opt)
      best f = L.minimumBy (compare `on` soccost em . S.fromList)
            $ edges <$> filter f sts
      bne = best (isNEin em)
      bgne = best (isGNEin em)
      g = soccost em (S.fromList bne) / soccost em (S.fromList bgne)
  in GNENERes{gap = g, bestne = bne, bestgne = bgne}

isGNEin :: (Ord a, Real b, Fractional b, Ord b) => WeightedEdges a b -> ChildMap a -> Bool
isGNEin em tcm =
  let nodes = S.toList $ nodesOf em
      t = toTree (rootChildMap tcm) tcm
      r = root t
      sps = M.fromList $
        map (\v -> let (nm, g) = toGraph em
                in case spLength (nm M.! r) (nm M.! v) g of
                    Just l -> (v,l)
            )
          nodes
      costs = M.fromList $
        map
          (\v -> let
              p = (map undirect . nodesToPath) $ rootPaths t M.! v
              c = sum $ (\pe -> (em M.! pe) / fromIntegral (congestion t pe)) <$> p
            in (v,c)
          )
          nodes
  in all (\v -> costs M.! v <= sps M.! v) nodes

toGraph :: Ord a => WeightedEdges a b -> (M.Map a G.Node , G.Gr a b)
toGraph em =
  let myNodes = S.toList $ nodesOf em
      nm = M.fromList $ zip myNodes [1..]
      gNodes = M.elems nm
      es = concatMap
        (\(e,w) ->
          let [u,v] = S.toList e
          in [(nm M.! u, nm M.! v, w), (nm M.! v, nm M.! u, w)]
        )
        $ M.toList em
  in (nm, G.mkGraph ( swap <$> M.toList nm) es)


class (Ord a, Show a) => Node a

instance Node Int

instance Node (Int,Int)
instance Node [Int]
