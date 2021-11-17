{-# language TupleSections, GADTs, FlexibleContexts, RankNTypes, PatternSignatures  #-}

module Prog where

import qualified Data.Map as M
import qualified Data.Maybe as Mb
import qualified Data.Set as S
import qualified Data.List as L
import Data.Function (on)
import Control.Monad (forM_, forM, foldM, guard, when, filterM, liftM)
import Language.SMTLib2
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Pipe
import Language.SMTLib2.Debug (debugBackend', DebugBackend)
import System.IO
import System.IO.Error
import System.IO.Temp
import Control.Exception (try, catch, ErrorCall, throw, IOException)
import Control.Concurrent.Async (async, wait, waitAnyCatchCancel, uninterruptibleCancel)
import Control.Concurrent.MVar
import Control.Concurrent (threadDelay)
import System.CPUTime
import System.Clock
import qualified Data.Graph.Inductive.PatriciaTree as G
import qualified Data.Graph.Inductive.Graph as G

import GraphHelper hiding (soccost)
import Pruefer
import Language

plus_ [] = creal 0
plus_ [x] = x
plus_ xs = plus xs

linearComb xs = plus_ $ (\(x,c) -> creal c .*. x ) <$> xs

sharing l x = l x / fromIntegral x

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


soccost l xs t = linearComb $ map (\e -> (xs M.! e, l (congestion t e))) $ edges $ toChildMap t



data Prog a where
  Prog ::
   ( forall b . Backend b
       => (Int -> Rational) -> Bool -> Bool
          -> Tree a
          -> Tree a
          -> [Edge a]
          -> [ChildMap a]
          -> Rational
          -> SMT b (Maybe [(Edge a, Rational)])
   )
          -> Prog a
prog ::( Node a) => Prog a
{-
  (Int -> Rational) -> -- cost sharing scheme
  Bool -> -- True = PoS, False = PoA
  Bool -> -- True = normalized (soc cost of = 1)
  Tree a -> -- "optimum" tree
  Tree a -> -- equilibrium tree
  [Edge a] -> -- edges in graph
  [ChildMap a] -> -- spanning trees to consider
  Rational -> -- lower bound on the ratio soccost ne / soccost opt
  SMT b (Maybe [(Edge a, Rational)])
-}
prog = Prog $ \ l pos norm opt ne es sts r -> do
  let optes = edges $ toChildMap opt
      optRootPaths = rootPaths opt
      nes = edges $ toChildMap ne
  xs <- M.fromList <$> mapM ( \e -> (e,) <$> declareVar real ) es

  forM_ sts $ \t -> do
    assert (soccost l xs (toTree (root opt) t) .>=. soccost l xs opt)

  -- no minimum spanning tree is equilibrium
  forM_ sts $ \st -> do
    assert $ (soccost l xs (toTree (root opt) st) .<=. soccost l xs opt)
      .=>. or' (
        map (\e -> do
            ((vul, vur), (uvl, uvr)) <- cnstr l xs (toTree (root opt) st) e
            (vul .<. vur) .|. (uvl .<. uvr)
          )
          (es L.\\ edges st)
        )
  -- ne is equilibrium
  forM_ (es L.\\ nes) $ \e -> do
     ((vul, vur), (uvl, uvr)) <- cnstr l xs ne e
     assert $ vul .>=. vur
     assert $ uvl .>=. uvr


  when pos (
  -- if a spanning tree is an equilibrium, then the social cost is not smaller than soccost ne
    forM_ sts $ \st -> do
      if st /= toChildMap ne
        then assert $
          and' (map
              (\e -> do
                ((vul, vur), (uvl, uvr)) <- cnstr l xs (toTree (root opt) st) e
                (vul .>=. vur) .&. (uvl .>=. uvr)
              )
              (es L.\\ edges st) )
              .=>.
              soccost l xs ne .<=. soccost l xs (toTree (root opt) st)

              -- or' $ reverse $ ((soccost nes) .<=. (soccost $ edges st)) : do
              --   e <- es L.\\ (edges st)
              --   ((vul, vur), (uvl, uvr)) <- cnstr xs (toTree (root opt) st) e
              --   [(vul .<. vur), (uvl .<. uvr)]
      else assert true
      )
  -- C(ne) >= r C(opt)
  assert $ soccost l xs ne .>. creal r .*. soccost l xs opt

  when norm
    (assert $ soccost l xs opt .==. creal 1)

  forM_ es $ \e ->
    assert $ xs M.! e .>=. creal 0

  r <- checkSat
  case r of
    Sat -> do
      xvals <-forM (M.toList xs) $ \(e,x) -> do
            m <- getModel
            ~(RealValue vx) <- modelEvaluate m x
            return (e,vx)
      return $ Just xvals
    _ -> return Nothing

data Parameters = Parameters {
    sharingscheme :: Int -> Rational
  , posswitch :: Bool
  , normalizeswitch :: Bool
  , debugfile :: Maybe String
  , systemsfile :: Maybe String
  , completeswitch :: Bool
  }

debugswitch = Mb.isJust . debugfile
showsystems = Mb.isJust . systemsfile

mach params opt ne r act pids = do
  start <- getTime Monotonic
  (x, p) <- waitAnyCatchCancel pids
  end <- getTime Monotonic
  forM_ pids uninterruptibleCancel
  let time = fromIntegral ( toNanoSecs $ diffTimeSpec end start) / (10^9)
  when (debugswitch params)
    (catch (
      appendFile (Mb.fromJust $ debugfile params) $
        show time ++ " :" ++ pprint (opt,ne) ++ " " ++ pprint r ++ "\n"
        )
        (\e -> do
                let err = (e :: IOException)
                hPutStr stderr $ show err
                threadDelay 1
                appendFile (Mb.fromJust $ debugfile params) $
                  show time ++ " :" ++ pprint (opt,ne) ++ " " ++ pprint r ++ "\n"
        )
    )
  when (debugswitch params && time > 60) $ hPutStrLn stderr $
    "this took " ++ show time ++ " sec."
    ++ pprint (opt, ne) ++ pprint r
  case p of
    Left err -> catch (throw err)
                (\e -> do
                  hPrint stderr (e :: ErrorCall)
                  hPrint stderr "trying again"
                  act)
    Right s -> return s


run program params solvers opt ne es sts r = do
  let be (solver, args) =  withBackendExitCleanly ( createPipe solver args)
                  $
                   mapM_ setOption
                    [ProduceModels True, SMTLogic "QF_LRA"]
                    >> case program of
                         Prog p -> p (sharingscheme params) (posswitch params) (normalizeswitch params) opt ne es sts r


  pids <- forM solvers $ async . be
  mach params opt ne r (run program params solvers opt ne es sts r) pids

runShowSystems program params solvers opt ne es sts r = do
  fh <- openFile (Mb.fromJust $ systemsfile params) WriteMode
  let be (solver, args) =  withBackendExitCleanly (
          debugBackend' False False Nothing fh
          <$> createPipe solver args
          )
                  $
                   mapM_ setOption
                    [ProduceModels True, SMTLogic "QF_LRA"]
                    >> case program of
                         Prog p -> p (sharingscheme params) (posswitch params) (normalizeswitch params) opt ne es sts r
  pids <- forM solvers $ async . be
  res <- mach params opt ne r (runShowSystems program params solvers opt ne es sts r) pids
  hClose fh
  return res

runOne' program params solvers opt ne es sts step old@(oldr, Just oldsol) = do
  let pos' v = soccost' (sharingscheme params) ne (M.fromList v) /
               soccost' (sharingscheme params) opt (M.fromList v)
      nextr = max (oldr + step) (pos' oldsol)
  when (debugswitch params)
    $ hPutStrLn stderr
        $ pprint (opt, ne) ++ " " ++ pprint nextr
  s <- if showsystems params
        then runShowSystems program params solvers opt ne es sts nextr
        else run program params solvers opt ne es sts nextr
  case s of
    Nothing -> do
       when (debugswitch params) $ hPutStrLn stderr $ pprint (opt,ne) ++ "end"
       return old
    (Just xs) -> do
      -- runOne' program l b norm sol opt ne es sts step (oldr + step, Just xs)
      runOne' program params solvers opt ne es sts step (nextr, Just xs)


runOne program params solvers opt ne es sts step r = do
    s <- if showsystems params
          then runShowSystems program params solvers opt ne es sts r
          else run program params solvers opt ne es sts r
    case s of
      Nothing -> do
        when (debugswitch params) $ hPutStrLn stderr $ pprint (opt,ne) ++ "end"
        return (r, Nothing)
      Just xs -> runOne' program params solvers opt ne es sts step (r, Just xs)

-- runTrees deb showsys nb opt ne solver l r step = do
runTrees params opt ne solver r step = do
  let es = if completeswitch params
            then edgesOfComplete (size opt)
            else edgesInUnion opt ne
      ts = allSpanningTreesAt (root opt) es (init $ edges $ toChildMap opt)
      -- sts = if nb
      --   then map toChildMap $ L.nubBy isomorph $ map (toTree (root opt)) ts
      --   else ts
  runOne prog params solver opt ne es ts step r

runMore program params solver opt nes es sts r step =
    mapM (\ne -> runOne program params solver opt ne es sts step r) nes




runWithFixedOpt params solver opt fes fsts step = do
  foldM
    (\(r, _) neseq -> do
      hPrint stderr neseq
      let ne = toTree (root opt) (fromPruefer neseq)
      runOne prog params solver opt  ne (fes opt ne) (fsts opt ne) step r
    )
    (1,Nothing)
    (allPrfseqs $ size opt)

runParallel program params solvers opt nes fes fsts r step = do
  lock <- newMVar ()
  let atomPut s = withMVar lock $ \_ -> hPutStrLn stderr s
  pids <- forM nes $ \ne ->
     async $ do
       atomPut $ pprint (opt, ne) ++ " " ++ pprint r ++ " start"
       runOne program params solvers opt ne (fes opt ne) (fsts opt ne) step r
  rs <- forM pids wait
  return $ zip nes rs


runWithFixedOptParallel program params solver p opt nes fes fsts step ir = do
  let go nes' (currr, oldsol) = do
       if null nes'
         then return (currr, oldsol)
         else do
           rs <- runParallel program params solver opt (take p nes') fes fsts currr step
           case filter (Mb.isJust . snd . snd) rs of
              [] -> go (drop p nes') (currr, oldsol)
              frs -> do
                let (ne, (rm, Just sol)) = L.maximumBy (compare `on` (fst . snd)) frs
                    m = (rm, Just (ne,sol))
                hPutStrLn stderr $ pprint m
                go (drop p nes') m
  go nes (ir, Nothing)

runWithFixedOptParallel' params solver p opt es =
  runWithFixedOptParallel prog params solver p opt
    ( toTree (root opt) <$> allSpanningTreesAt (root opt) es (init $ edges $ toChildMap opt))


runParallelNE program params solvers ne opts fes fsts r step = do
  lock <- newMVar ()
  pids <- forM opts $ \opt -> do
      when (debugswitch params)
        $ withMVar lock
          $ \_ -> hPutStrLn stderr $ pprint (opt,ne) ++ " " ++ pprint r ++ " start"
      async $ runOne program params solvers opt ne (fes opt ne) (fsts opt ne) step r
  rs <- forM pids wait
  when (debugswitch params) $ hPutStrLn stderr "----"
  return $ zip opts rs

runWithFixedNEParallel program params solver p ne opts fes fsts step ir =
  let go opts' (currr, oldsol) = do
       if null opts'
         then return (currr, oldsol)
         else do
           rs <- runParallelNE program params solver ne (take p opts') fes fsts currr step
           case filter (Mb.isJust . snd . snd) rs of
              [] -> go (drop p opts') (currr, oldsol)
              frs -> do
                let (opt, (rm, Just sol)) = L.maximumBy (compare `on` (fst . snd)) frs
                    m = (rm, Just (opt,ne,sol))
                hPutStrLn stderr $ pprint m
                go (drop p opts') m
  in go opts (ir, Nothing)

runWithFixedNEParallel' nb params solver p ne step ir =
  let ts' = map (toTree (root ne) . fromPruefer)
              $ allPrfseqs $ size ne
      ts = if nb then L.nubBy isomorph ts' else ts'
  in runWithFixedNEParallel prog params solver p ne
      ts step ir

runAll params r es st fes fsts solver p start step = do
  foldM
    (\old@(oldr, oldsol) opt -> do
       hPutStrLn stderr ""
       hPutStrLn stderr $ "opt: " ++ pprint opt
       res@(r', msol) <- runWithFixedOptParallel' params solver p opt es fes fsts step oldr
       case msol of
         Nothing -> return old
         Just sol ->
           if r' > oldr
             then do
               -- hPutStrLn stderr $ show $ fromRational r'
               return (r', Just (opt,sol))
             else
               return old
    )
    (start, Nothing)
    (L.nubBy isomorph $ toTree r <$> allSpanningTreesAt r es (init st))

solveProg params rt opt ne solvers r = do
  let es o n = if completeswitch params
        then edgesOfComplete $ size o
        else edgesInUnion o n
  pids <- forM solvers (\(solver,args) -> async
    (withBackend (createPipe solver args) $
      mapM_ setOption [SMTLogic "QF_LRA", ProduceModels True]
      >> case prog of
       Prog p -> p (sharingscheme params) (posswitch params) (normalizeswitch params) opt ne
          (es opt ne)
          ( allSpanningTreesAt rt (es opt ne) (init $ edges $ toChildMap opt))
          r))
  (_, p) <- waitAnyCatchCancel pids
  case p of
    Left err -> catch (throw err)
                (\e -> do
                  hPrint stderr (e :: ErrorCall)
                  hPrint stderr "trying again"
                  solveProg params rt opt ne solvers r
                )
    Right s -> return s


solveParallelFixedOPT program params rt opt nes solvers r = do
  pids <- forM nes $ \ne -> async $ solveProg params rt opt ne solvers r
  rs <- forM pids wait
  return $ zip nes rs

solveParallelFixedNE params rt ne opts solvers r = do
  pids <- forM opts $ \o -> async $ solveProg params rt o ne solvers r
  rs <- forM pids wait
  return $ zip opts rs


findAllFixedNE' params sol p r ne opts = do
  let rt = root ne
      go [] xs = return xs
      go os acc = do
        ps <- solveParallelFixedNE params rt ne (take p os) sol r
        go (drop p os) $ filter (Mb.isJust . snd) ps ++ acc
  go opts []

findAllFixedNE nb params solver c ne r = do
  let rt = root ne
      ts = map (toTree (root ne) . fromPruefer)
        $ allPrfseqs $ size ne
      opts = if nb
        then L.nubBy isomorph ts
        else ts
  findAllFixedNE' params solver c r ne opts

findAll params sol c n r = do
  let ts = L.nubBy isomorph $ map (toTree 1 . fromPruefer)
        $ allPrfseqs n
  xs <- forM ts $ \ne -> do
          os <- findAllFixedNE False params sol c ne r
          return $ map (\(o,x) -> (o,ne,x)) os
  return $ concat xs

runAllDisjoint params n complete solver p step = do
  let allseqs = map fromPruefer (allPrfseqs n)
  foldM
    (\old@(oldr, oldsol) opt -> do
       let fes = if complete
                  then \opt ne -> edgesOfComplete n
                  else edgesInUnion
           fsts = \opt ne ->
                    let optes = edges $ toChildMap opt
                    in allSpanningTreesAt (root opt) (fes opt ne) (init optes)
       hPutStrLn stderr $ "opt: " ++ pprint opt
       let nes = map (toTree n) $ filter (treeDisjoint $ toChildMap opt) allseqs
       res@(r', msol) <- runWithFixedOptParallel prog params solver p opt nes fes fsts step oldr
       case msol of
         Nothing -> return old
         Just sol ->
           if r' > oldr
             then do
              hPrint stderr $ fromRational r'
              return (r', Just (opt,sol))
             else
               return old
    )
    (1, Nothing)
    (L.nubBy isomorph $ map (toTree n ) allseqs)

pos params es r st solver p step = do
  runAll params r es st (\_ _ -> es) (\_ _ -> allSpanningTreesAt r es (init st)) solver p step
