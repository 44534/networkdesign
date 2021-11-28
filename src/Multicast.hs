{-# Language FlexibleInstances, TupleSections, FlexibleContexts, GADTs #-}

module Multicast where

import Data.Maybe as Mb
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Map as M
import Language.SMTLib2
import Control.Monad

import GraphHelper hiding (congestion, soccost)
import Prog hiding (cnstr)

type MulticastNode a = (a, Bool)

instance Node (MulticastNode Int)
instance Node (MulticastNode (Int,Int))


-- kante gerichtet: down
congestion :: Ord a => Tree (MulticastNode a) -> Edge (MulticastNode a) -> Int
congestion t e =
  let cm = toChildMap t
  in if e `elem` edges cm
      then let (u,v) = dirOfEdge cm e
               subt = Mb.fromJust $ subTreeAt t v
           in length $ filter snd $ elements subt
      else 0

removeNonPlayerBranches :: Ord a => ChildMap (MulticastNode a) -> ChildMap (MulticastNode a)
removeNonPlayerBranches cm =
  if all snd $ leaves cm
    then cm
    else let nonPlayerLeaves = filter (not . snd) $ leaves cm
         in removeNonPlayerBranches $ foldl (flip removeLeave) cm nonPlayerLeaves

allSteinerTreesAt :: Ord a => MulticastNode a -> [Edge (MulticastNode a)] -> [Edge (MulticastNode a)] -> [ChildMap (MulticastNode a)]
allSteinerTreesAt r es nearst =
  let sts = allSpanningTreesAt r es nearst
  in L.nub $ removeNonPlayerBranches <$> sts

cnstr l xs ne e = do
  let [u,v] = S.toList e
      (upath, vpath) = applyToBoth (map undirect . nodesToPath) $ pathsToLca (rootPaths ne) u v
  return ( ( (xs M.! e) .+. linearComb (map (\e' -> (xs M.! e', sharing l (1 + congestion ne e')) ) vpath)
           , linearComb $ map (\e' -> (xs M.! e', sharing l (congestion ne e')) ) upath
           )
         , ( (xs M.! e) .+. linearComb (map (\e' -> (xs M.! e', sharing l (1 + congestion ne e')) ) upath)
           , linearComb $ map (\e' -> (xs M.! e', sharing l (congestion ne e')) ) vpath
           )
         )
cnstrQuasiBip l xs ne e1 e2 = do
  let [u] = S.toList e1 L.\\ S.toList e2
      [v] = S.toList e2 L.\\ S.toList e1
      (upath, vpath) = applyToBoth (map undirect . nodesToPath) $ pathsToLca (rootPaths ne) u v
  return ( ( (xs M.! e1) .+. (xs M.! e2) .+. linearComb (map (\e' -> (xs M.! e', sharing l (1 + congestion ne e')) ) vpath)
           , linearComb $ map (\e' -> (xs M.! e', sharing l (congestion ne e')) ) upath
           )
         , ( (xs M.! e1) .+. (xs M.! e2) .+. linearComb (map (\e' -> (xs M.! e', sharing l (1 + congestion ne e')) ) upath)
           , linearComb $ map (\e' -> (xs M.! e', sharing l (congestion ne e')) ) vpath
           )
         )

isNE l xs t es =
  forM_ (es L.\\ edges (toChildMap t)) $ \e -> do
    let [u,v] = S.toList e
        visited n = n `elem` elements t
    case (visited u, visited v) of
      (True,True) -> do
         ((vul, vur), (uvl, uvr)) <- cnstr l xs t e
         assert $ vul .>=. vur
         assert $ uvl .>=. uvr
      (True, False) -> forM_ (S.toList $ S.delete u (neighbors v $ S.fromList es) ) $ \v' -> do
        ((vul, vur), (uvl, uvr)) <- cnstrQuasiBip l xs t e (S.fromList [v,v'])
        assert $ vul .>=. vur
        assert $ uvl .>=. uvr
      (False, True) -> forM_ (S.toList $ S.delete v (neighbors u $ S.fromList es) ) $ \u' -> do
        ((vul, vur), (uvl, uvr)) <- cnstrQuasiBip l xs t e (S.fromList [u,u'])
        assert $ vul .>=. vur
        assert $ uvl .>=. uvr
      (False, False) -> error "not quasibip"


progQuasiBipartite :: Node a => Prog (MulticastNode a)
  -- (Backend b, Node a) =>
  -- (Int -> Rational) -> -- sharing scheme
  -- Bool -> -- True = PoS, False = PoA
  -- Bool -> -- True = normalized (cost of opt = 1)
  -- Tree (MulticastNode a ) -> Tree (MulticastNode a )
  -- -> [Edge (MulticastNode a )] -> [ChildMap (MulticastNode a )]
  -- -> Rational -> SMT b (Maybe [(Edge (MulticastNode a ), Rational)])
progQuasiBipartite = Prog $ \ l pos norm opt ne es sts r -> do
  let optes = edges $ toChildMap opt
      nes = edges $ toChildMap ne
      steinertrees = allSteinerTreesAt (root opt) es (init optes)
  xs <- M.fromList <$> mapM ( \e -> (e,) <$> declareVar real ) es

  -- opt is opt
  forM_ steinertrees $ \t -> do
      assert (soccost l xs (toTree (root opt) t) .>=. soccost l xs opt)

  -- ne is ne
  isNE l xs ne es


  when pos (
  -- if other spanning tree (st) is equilibrium, then the social cost has to be at least as large
    forM_ sts $ \st -> do
      if st /= toChildMap ne
        then assert $ and' (map
              (\e -> do
                  let [u,v] = S.toList e
                      stt = toTree (root opt) st
                      visited n = n `elem` elements stt
                  case (visited u, visited v) of
                    (True,True) -> do
                       ((vul, vur), (uvl, uvr)) <- cnstr l xs stt e
                       (vul .>=. vur) .&. (uvl .>=. uvr)
                    (True, False) -> and' $ flip map (S.toList $ S.delete u (neighbors v $ S.fromList es) ) $ \v' -> do
                      ((vul, vur), (uvl, uvr)) <- cnstrQuasiBip l xs stt e (S.fromList [v,v'])
                      (vul .>=. vur) .&. (uvl .>=. uvr)
                    (False, True) -> and' $ flip map (S.toList $ S.delete v (neighbors u $ S.fromList es) ) $ \u' -> do
                      ((vul, vur), (uvl, uvr)) <- cnstrQuasiBip l xs stt e (S.fromList [u,u'])
                      (vul .>=. vur) .&. (uvl .>=. uvr)
                    (False, False) -> error "not quasibip"
              )
              (es L.\\ edges st)
              )
              .=>.
              (soccost l xs ne .<=. soccost l xs  (toTree (root opt) st))
      else assert true
      )

  -- c(ne) >= r c(opt)
  assert $ soccost l xs ne .>. creal r .*. soccost l xs opt

  when norm
    (assert $ soccost l xs opt .==. creal 1)

  forM_ es $ \e ->
    assert $ xs M.! e .>. creal 0

  r <- checkSat
  case r of
    Sat -> do
      xvals <-forM (M.toList xs) $ \(e,x) -> do
            m <- getModel
            ~(RealValue vx) <- modelEvaluate m x
            return (e,vx)
      return $ Just xvals
    _ -> return Nothing

italianInstanceMulticast n =
  let fes = [S.fromList [(0, False),(i,True)] | i <- [1 .. n]]
      pes = [S.fromList [(i,True),(i+1,True)] | i <- [1 .. n-1]]
      es = fes ++ pes
      optes = S.fromList [(0, False),(1,True)]: pes
      opt = toTree (0,False) $ fromEdges (0,False) $ S.fromList optes
      ne = toTree (0,False) $ fromEdges(0,False) $ S.fromList fes
      sts = allSteinerTreesAt (0,False) es (init optes)
  in (opt,ne,es,sts)



doubleFan n =
  let es = concat [ [S.fromList [(0::Int,False), (i, True)], S.fromList [(n+1,False), (i, True)] ] | i <- [1 .. n] ]
      opt = Tree (0,False) [Tree (1,True) [ Tree (n+1,False) [ Tree (i,True) [] | i <- [2 .. n] ] ] ]
      ne = Tree (0,False) [Tree (i,True) [] | i <- [1 .. n]]
      sts = allSteinerTreesAt (0,False) es (init $ edges $ toChildMap opt)
  in (opt, ne, es, sts)

fanSub3Fans n =
  let topes = [ S.fromList [((0::Int, 0::Int),False), ((1,i), True)] | i <- [1 .. 2*n+1] ]
      botes = concat [ [S.fromList [((2,i), False), ((1,i+j),True)] | j <- [0,1,2]] | i <- [1,3 .. 2*n]]
      es = topes ++ botes
      optes = S.fromList [((0::Int, 0::Int),False), ((1,1),True)] :
        botes
      opt = toTree ((0::Int, 0::Int),False) $ fromEdges ((0::Int, 0::Int),False) $ S.fromList optes
      ne = toTree ((0::Int, 0::Int),False) $ fromEdges ((0::Int, 0::Int),False) $ S.fromList topes
      sts = allSteinerTreesAt ((0::Int, 0::Int),False) es (init optes)
  in (opt, ne, es, sts)
