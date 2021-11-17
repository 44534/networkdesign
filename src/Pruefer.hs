module Pruefer where

import qualified Data.Map.Strict as M
import qualified Data.List as L
import qualified Data.Set as S
import Control.Monad (replicateM)

import GraphHelper

type PrfSeq = [Int]

fromPruefer_ :: PrfSeq -> ChildMap Int -> M.Map Int Int -> ChildMap Int
fromPruefer_ [] currm nm =
  let [u,v] = M.keys $ M.filter (0 /=) nm
      ma = max u v
      mi = min u v
  in M.unionWith S.union (M.fromList [(ma, S.singleton mi), (mi, S.empty) ]) currm
fromPruefer_ (n:pseq) currm nm =
  let
    (l, _) = M.findMin $ M.filter (1 ==) nm
    newnm = M.adjust (+ (-1)) n $ M.delete l nm
    newm = M.unionWith S.union (M.fromList [(n, S.singleton l), (l, S.empty)]) currm
  in fromPruefer_ pseq newm newnm


fromPruefer :: PrfSeq -> ChildMap Int
fromPruefer pseq =
  let
    ns = [1 .. length pseq + 2]
    nm = M.fromList $ map (\v -> (v, 1 + length (L.elemIndices v pseq))) ns
  in fromPruefer_ pseq M.empty nm

pathPruefer n = reverse [1 .. n - 2]

pathTree n = toTree n (fromPruefer $ pathPruefer n)

starPruefer n = replicate (n-2) n

starTree n = toTree n (fromPruefer $ starPruefer n)

allPrfseqs :: Int -> [PrfSeq]
allPrfseqs n = replicateM (n-2) [1 .. n]

levelTreesInBinaryOfHeight :: Int -> [Tree Int]
levelTreesInBinaryOfHeight 0 = [Tree 1 []]
levelTreesInBinaryOfHeight 1 = [Tree 1 [Tree 2 [Tree 3 []]]]
levelTreesInBinaryOfHeight h =
  let lpaths = concatMap (map (\x -> S.fromList [x, x+1]) . init . levelOfBinary ) [0 .. h]
      connectTrees = L.nubBy isomorph $ map (toTree 1 . fromPruefer ) $ allPrfseqs $ h + 1
      possConnectLevels l1 l2 = (\x y -> S.fromList [x,y]) <$> levelOfBinary l1 <*> levelOfBinary l2
  in L.nubBy isomorph $ do
      t <- connectTrees
      let connectEdges = traverse (uncurry possConnectLevels . (\e -> let [u,v] = S.toList e in (u-1,v-1)) )
              $ edges $ toChildMap t
      cones <- connectEdges
      return $ toTree 1 $ fromEdges 1 $ S.fromList lpaths `S.union` S.fromList cones
