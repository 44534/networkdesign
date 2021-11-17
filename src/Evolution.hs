{-# Language ScopedTypeVariables, FlexibleInstances, DatatypeContexts #-}

module Evolution where

import GraphHelper
import System.Random
import System.IO (hFlush, stdout)
import Control.Monad
import qualified Data.Map.Strict as M
import qualified Data.List as L
import qualified Data.Set as S
import Control.Concurrent.Async
import Data.Ord

minWeight = 0.0001
maxWeight = fromIntegral

data Source = Init | Italy | Randup | Decopt | Incne | Optclo
  deriving Show



data Node a => Individuum a = Individuum {
  graph :: !(WeightedEdges a Double),
  rt :: !a,
  measure :: Measure,
  value :: !(Res a Double),
  source :: ! [Source]
 }
  deriving Show

data Measure = POS | GNENE
  deriving Show

res' :: Node a => (Measure, a, WeightedEdges a Double) -> Res a Double
res' (POS, r, insta) = pos r insta
res' (GNENE, r, insta) = gnenegap r insta

evaluate :: Node a => Individuum a -> Double
evaluate i =
    case measure i of
      POS -> ratio $ value i
      GNENE -> gap $ value i

randIndiv :: Measure -> Int -> IO (Individuum Int)
randIndiv m n = do
  let es =  edgesOfComplete n
  r <- randomRIO (1, n)
  ws <- replicateM (length es) $ randomRIO (minWeight, maxWeight n)
  let insta = M.fromList $ zip es ws
  return Individuum { graph = insta, rt = r, measure = m, value = res' (m, r, insta), source=[Init]}

italianInstance :: Int -> Individuum Int
italianInstance n =
  let r = 1
      eps = 1e-10
      starWeight i =
        if i == n || i == n-1
          then 9/5
          else 8/5 * (8/9)^(n-1-2-(i-1))
      starEdges = [(S.fromList [1,i], starWeight i) | i <- [2 .. n]]
      pathWeight i =
        if i == n - 1
          then 9/10 + eps
          else (8/9)^(n-1-1-i) + eps
      pathEdges = [(S.fromList [i, i+1], pathWeight i) | i <- [2 .. n-1]]
      allEdges = zip (edgesOfComplete n) $ repeat (fromIntegral n)
      es = [starEdges, pathEdges, allEdges]
      g = M.unions $ map M.fromList es
  in Individuum {graph = g, rt = r, measure = POS, value = pos r g, source=[Italy]}

randGrid :: Int -> Int -> IO (Individuum (Int,Int))
randGrid w h = do
  let es = edgesOfGrid w h
  ws <- replicateM (length es) $ randomRIO (minWeight, maxWeight (w*h))
  let insta = M.fromList $ zip es ws
      r = (1,1)
  return Individuum {graph = insta, rt = r, measure = POS, value = pos r insta, source = [Init]}

randRing :: Int -> IO (Individuum Int)
randRing n = do
  let es = map S.fromList $ [n,1] : [ [i, i+1] | i <- [1 .. n-1]]
  ws <- replicateM (length es) $ randomRIO (minWeight, maxWeight n)
  let insta = M.fromList $ zip es ws
      r = 1
  return Individuum {graph = insta, rt = r, measure = POS, value = pos r insta, source = [Init]}

type Population a = [Individuum a]

randSelect :: [a] -> IO a
randSelect xs | not (null xs) = do
  i <- randomRIO (0, length xs - 1)
  return $ xs !! i

updateWeightAt :: Node a => Source -> Individuum a -> Edge a -> Double -> Individuum a
updateWeightAt s i@(Individuum es rt m _ _) e w =
  let newind = M.adjust (const w) e es
      newval = res' (m, rt, newind)
  in Individuum { graph = newind, rt = rt, measure = measure i, value = newval, source = s : source i }


data Jump = Uniform | Biased

decOptEdge :: Node a => Jump -> Individuum a -> IO (Individuum a)
decOptEdge j i@(Individuum es _ _ (POSRes _ o _) _) = do
  e <- randSelect o
  w <- case j of
    Uniform -> randomRIO (minWeight, es M.! e)
    Biased -> do
      -- d <- (10**) <$> randomRIO(-3,0)
      d <- (^2) <$> randomRIO (0,2)
      return $ max minWeight $ es M.! e - d
  return $ updateWeightAt Decopt i e w

incNEEdge :: Node a => Jump -> Individuum a -> IO (Individuum a)
incNEEdge j i@(Individuum es _ _ (POSRes _ o b) _) = do
  e <- randSelect b
  let mw = maxWeight $ S.size $ nodesOf es
  w <- case j of
    Uniform -> randomRIO (es M.! e, mw)
    Biased -> do
      -- d <- (10**) <$> (randomRIO(-3,0))
      d <- (^2) <$> randomRIO (0,2)
      return $ min mw $ es M.! e + d
  return $ updateWeightAt Incne i e w



randUpdateEdge :: Node a => Jump -> Individuum a -> IO (Individuum a)
randUpdateEdge j i = do
  e <- randSelect $ M.keys $ graph i
  let mw = maxWeight $ S.size $ nodesOf $ graph i
  w <- case j of
    Uniform -> randomRIO (minWeight, mw)
    Biased -> do
      vz <- randSelect [negate, id]
      d <- (^3) <$> randomRIO (0,1)
      return $ max minWeight $ min mw $ graph i M.! e + vz d
  return $ updateWeightAt Randup i e w

moreEdges :: (Individuum a -> IO (Individuum a)) -> Int -> Individuum a -> IO (Individuum a)
moreEdges f u i = do
  k <- randomRIO (1, u)
  foldM (\i _ -> f i) i [1 .. k]

decOptEdges j = moreEdges (decOptEdge j)
incNEEdges j = moreEdges (incNEEdge j)
randUpdateEdges j = moreEdges (randUpdateEdge j)


optCloserToPath :: Node a => Individuum a -> IO (Individuum a)
optCloserToPath i@(Individuum es r _ (POSRes _ o b) _) =
  let opt = fromEdges r $ S.fromList o
  in if length (leaves opt) == 1
    then return i
    else do
          v <- randSelect $ S.toList $ nodesOf $ graph i
          l <- randSelect $ L.delete v $ leaves opt
          -- let pev = S.fromList [v, parent opt v]
          return $ updateWeightAt Optclo i (S.fromList [v,l]) minWeight

nextGen :: Node a => Measure -> Int -> (Individuum a -> Double) -> Population a -> IO (Population a)
nextGen m k val p = do
  let fs = case m of
        POS -> []
          <> [ decOptEdges Biased 2, incNEEdges Biased 2 ]
          <> [ randUpdateEdges Uniform 2 ]
          -- <> [ optCloserToPath ]
        GNENE -> [ randUpdateEdges Uniform 2 ]
  i <- randomRIO (0,length p - 1)
  let (pre, post) = splitAt i p
      rot =  post <> pre
      (vorn,hint) = splitAt (2*k) rot
      (vo,rn) = splitAt k vorn
  children <- concat <$> forConcurrently vo (\i -> forConcurrently fs (\ f -> do
    c <- f i
    value c `seq` return c
    ))
  let rn' = take k $ L.sortOn (Data.Ord.Down . val) $ children <> rn
  return $ vo <> rn' <> hint

live :: Node a => Measure -> Int -> Population a -> IO ()
live m k pop = do
  let go p curr = do
              n <- nextGen m k evaluate p
              let r = evaluate $ head n
              -- print (curr, r)
              if r <= curr
                then do
                      putStr "."
                      hFlush stdout
                      go n curr
                else do
                      print r
                      print $ head n
                      go n r
  go pop 1

liveRand :: Measure -> Int -> Int -> Int -> IO ()
liveRand m nrNodes sizeStart sizeKeep = do
  start <- replicateM sizeStart $ randIndiv m nrNodes
  live m sizeKeep start
