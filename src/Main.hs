module Main where

import System.Environment
import Options.Applicative
import Options.Applicative.Extra
import Data.Char
import Data.Maybe as Mb
import Data.Ratio
import Control.Monad
import Data.Ord (comparing)
import Data.List as L
import qualified Data.Set as S
import System.IO

import Prog
import Pruefer
import GraphHelper
import Evolution (liveRand, live, italianInstance, randIndiv, randGrid, randRing, Measure(..))
import Multicast
import Language

import Language.SMTLib2.Pipe


data EnumType = All Int | Path Int | Disj Int | Star Int | BinTree Int |
  Grid {w :: Int, h :: Int} | Wheel Int | Cube Int | FanOfFans Int Int |
  TwoPaths Int | TwoPathsWithPoS Int Rational

data PTyp = PoS | PoA

data Insta = DoubleFan Int | FanSub3Fans Int | Italian Int

data EnumMod = Enum | Find

data EvolutionType =
   Rand | Ring | Fan | EGrid {ewidth :: Int, eheight :: Int}


data Modus = EnumFind {
    mod :: EnumMod
  , typ :: EnumType
  , backend :: String
  , cores :: Int
  , start :: Rational
  , step :: Rational
  , compl :: Bool
  , ptyp :: PTyp
  , normalize :: Bool
  , inf :: Bool
  , deb :: Maybe String
  , showsystemsopt :: Maybe String
  }
  | Evolution {
      etyp :: EvolutionType
    , nrNodes :: Int
    , startSize :: Int
    , keepSize :: Int
    , meas :: String
    }
  | QuasiBip {
      insta :: Insta
    , backend :: String
    , step :: Rational
    }

data Sharing = Fair | Harmonic |
    Linear {
      shareattwo :: Rational
    , shareslope :: Rational }
  | Power Rational

data ArgOpts = ArgOpts {
    modus :: Modus
  , share :: Sharing
  , pp :: Bool
}

newtype R = R { unR :: Rational}

readRational__ :: ReadS R -- NB: doesn't handle leading "-"
readRational__ r = do
     (n,d,s) <- readFix r
     (k,t)   <- readExp s
     return (R $ (n%1)*10^^(k-d), t)
 where
     readFix r = do
        (ds,s)  <- lexDecDigits r
        (ds',t) <- lexDotDigits s
        return (read (ds++ds'), length ds', t)

     readExp (e:s) | e `elem` "eE" = readExp' s
     readExp s                     = return (0,s)

     readExp' ('+':s) = readDec s
     readExp' ('-':s) = do (k,t) <- readDec s
                           return (-k,t)
     readExp' s       = readDec s

     readDec s = do
        (ds,r) <- nonnull isDigit s
        return (foldl1 (\n d -> n * 10 + d) [ ord d - ord '0' | d <- ds ],
                r)

     lexDecDigits = nonnull isDigit

     lexDotDigits ('.':s) = return (span' isDigit s)
     lexDotDigits s       = return ("",s)

     nonnull p s = do (cs@(_:_),t) <- return (span' p s)
                      return (cs,t)

     span' _ xs@[]         =  (xs, xs)
     span' p xs@(x:xs')
               | x == '_'  = span' p xs'   -- skip "_" (#14473)
               | p x       =  let (ys,zs) = span' p xs' in (x:ys,zs)
               | otherwise =  ([],xs)

instance Read R where
  readsPrec p s = readRational__ s

argOpts :: Parser ArgOpts
argOpts = ArgOpts
  <$> (
      ( EnumFind <$>
          (   flag' Enum (long "enum"
              <> help "enumerate all instances trying to find the highest PoS")
          <|> flag' Find (long "find"
              <> help "find all instances that achieve a given value for the PoS" )
          )
      <*>
        (   All <$> option auto (long "all"
                      <> metavar "NrNodes"
                      <> help "all pairs of trees with NrNodes nodes are considered for OPT and NE")
        <|> Path <$> option auto (long "path"
                      <> metavar "NrNodes"
                      <> help "OPT is fixed to be a path of length NrNodes having the root as one endpoint")
        <|> Disj <$> option auto (long "disj"
                      <> metavar "NrNodes"
                      <> help "only edge-disjoint trees with NrNodes nodes are considered for OPT and NE")
        <|> Star <$> option auto (long "star"
                      <> metavar "NrNodes"
                      <> help "NE is fixed to be the star with the root as center and NrNodes nodes")
        <|> Wheel <$> option auto (long "wheel"
                      <> metavar "NrNodes"
                      <> help "the underlying graph is the wheel with NrNodes nodes")
        <|> Cube <$> option auto (long "cube"
                      <> metavar "DIM"
                      <> help "the underlying graph is the DIM-dimensional cube")
        <|> TwoPaths <$> option auto (long "twopaths"
                      <> metavar "NrNodes"
                      <> help "OPT is the path 1-...-NrNodes, all other paths are considered as NE")
        <|> (FanOfFans <$>
                    option auto (long "fof-b"
                      <> metavar "NrNodes"
                      <> help "size of each fan in the second level")
                <*> option auto (long "fof-t"
                      <> metavar "NrNodes"
                      <> help "nr of nodes in the first level"
                      )
            )
        <|> BinTree <$> option auto (long "bintree"
                          <> metavar "HEIGHT"
                          <> help "NE is fixed to be the complete binary tree of height HEIGHT, OPTs consist of the level paths with all possible connections"
                          )
        <|> ( Grid <$>
                    option auto (long "grid-w"
                      <> metavar "WIDTH"
                      <> help "the underlying graph is the WIDTH x HEIGHT grid")
                <*> option auto (long "grid-h"
                      <> metavar "HEIGHT"
                      <> help "the underlying graph is the WIDTH x HEIGHT grid")
            )
        )
      <*> strOption (long "backend" <> short 'b'
            <> metavar "NAME"
            <> help "the smt solver to be used, currently available options: z3, cvc4, opensmt, yices"
            )
      <*> option auto (long "cores" <> short 'c' <> value 1
            <> metavar "NR"
            <> help "the number of parallel computations to be done, waiting for all to finish. This has to be combined with the \"+RTS\" option")
      <*> (unR <$> option auto (long "start"
                    <> metavar "VALUE"
                    <> help "A lower bound on the PoS. Resulting instances will have PoS > VALUE."
                    )
          )
      <*> (unR <$> option auto (long "step" <> short 's'
                    <> help "The value to increment the ratio in each step when enumerating. Has no affect for \"--find\"."
                    )
          )
      <*> switch (long "complete"
            <> help "Whether to consider the complete graph or just the union of OPT and NE tree (default). Relevant only for --all, --path and --star."
            )
      <*> (   flag' PoS (long "pos"
                <> help "whether to consider the PoS ..." )
          <|> flag' PoA (long "poa"
                <> help "... or PoA")
          )
      <*> switch (long "normalize"
              <> help "whether to normalize the social cost of OPT to 1")
      <*> switch (long "continue"
              <> help "run forever increasing NrNodes")
      <*> (optional $ strOption (long "debug"
              <> metavar "FILENAME"
              <> help "verbose output and saves times in FILENAME.")
          )
      <*> (optional $ strOption (long "showsystems"
              <> metavar "FILENAME"
              <> help "Save systems sent to solver in FILE")
          )
    )
    <|> (Evolution <$>
          (   flag' Rand (long "random"
                <> help "evolution of random instances. Every edge of the complete graph gets a random weight between 0 and nrNodes.")
          <|> flag' Ring (long "ring"
                <> help "evolution of random ring instances.")
          <|> flag' Fan (long "fan"
                <> help "evolution of random fan instance.")
          <|> ( EGrid <$>
                    option auto (long "width" <> short 'w')
                <*> option auto (long "height" <> short 'h'
                      <> help "evolution of random w x h grid instances.")
              )
          )
         <*> option auto (long "nrNodes" <> short 'n'
              <> help "number of nodes of the instances. Has no effect on grid instances.")
         <*> option auto (long "startN" <> short 's'
              <> help "the number of individuals in the initial population")
         <*> option auto (long "keepN" <> short 'k'
              <> help "the number of individuals to keep in each generation")
         <*> strOption (long "measure" <> short 'm'
              <> metavar "pos | gnene"
              <> help "the evaluation function. Either PoS or C(best NE)/C(best go-it-alone NE)")
        )
    <|> ( QuasiBip <$>
            (   DoubleFan <$> option auto (long "qbip-2fan")
            <|> FanSub3Fans <$> option auto (long "qbip-fan3fans")
            <|> Italian <$> option auto (long "qbip-italian")
            )
          <*> strOption (long "backend" <> short 'b')
          <*> (unR <$> option auto (long "step" <> short 's'))
        )
    )
    <*> (    flag' Fair (long "fair"
              <> help "fair cost sharing f(k) = 1/k")
        <|> flag' Harmonic (long "harmonic"
              <> help "f(k) = H(k) / k")
        <|> (Linear <$>
                (unR <$> option auto (long "sharing2"
                            <> help "the value of 2f(2)"
                            )
                )
            <*> (unR <$> option auto (long "sharingslope"
                          <> help "the slope of kf(k). f(1) = 1, f(2) = sharing2 / 2, f(k) = (sharing2 + slope * (k-2)) / k")
                          )
            )
        <|> (Power . unR <$> option auto (long "power"
                              <> metavar "A"
                              <> help "f(k) = k^(A-1)") )
        )
    <*> switch (long "no-prettyprint"
                 <> help "turn off pretty print")


outend pp r = hPutStrLn stderr "--------" >> out pp r

out :: (Show a, PPrint a) => Bool -> a -> IO ()
out nopretty r =
  if nopretty then print r else putStrLn $ pprint r

z3 = ("z3", ["-smt2","-in"])
cvc4 = ("cvc4", [ "--lang", "smt" ])
opensmt = ("opensmt", ["-p"])
yices = ("yices-smt2", ["--smt2-model-format"])

allsolvers = [cvc4, opensmt, yices]

toFunc Fair = const 1
toFunc Harmonic = \k -> sum [1.0/fromIntegral i | i <- [1::Int .. k]]
toFunc (Linear at2 slope) = \k -> (1: iterate (slope + ) at2) !! (k-1)
toFunc (Power a) = \k -> toRational $ (fromIntegral k :: Double) ** (fromRational a :: Double)


main :: IO ()
main = do
  args <- execParser $ 
                info (helper <*> argOpts) 
                     (fullDesc <> progDesc "networkdesign" <> header "Enumeration of instances to find lower bounds on the Price of Stability in broadcast games using an SMT solver.")
  let l = toFunc $ share args
  case modus args of
    EnumFind et t b c start s cpl pt norm inf debug showsys -> do
      let solvers = case b of
            "z3" -> [z3]
            "cvc4" -> [cvc4]
            "opensmt" -> [opensmt]
            "yices" -> [yices]
            "all" -> allsolvers
          fes n = if cpl
                 then \opt ne -> edgesOfComplete n
                 else edgesInUnion
          fsts = \opt ne ->
                   let optes = edges $ toChildMap opt
                   in allSpanningTreesAt (root opt) ((fes $ size opt) opt ne) (init optes)
          pos = case pt of
            PoS -> True
            PoA -> False
          run rt es st = runAll params rt es st (\_ _ -> es)
              (\_ _ -> allSpanningTreesAt rt es (init st))
          ns x = if inf then [x ..] else [x]
          compute pp xs act = foldM_ (\r n -> do
                    print n
                    res@(newr,_) <- act r n
                    outend pp res
                    hFlush stdout
                    return newr
                    )
                    start
                    xs
          params = Parameters {
                    sharingscheme = l
                   , posswitch = pos
                   , normalizeswitch = norm
                   , debugfile = debug
                   , systemsfile = showsys
                   , completeswitch = cpl
                   }
      case et of
        Enum -> do
          case t of
            All n -> compute (pp args) (ns n)
              $ \r n -> runAll params 1 (edgesOfComplete n) (canonicalSpanningTreeOfComplete n) (fes n) fsts solvers c r s

            Path n -> compute (pp args) (ns n)
              $ \r n -> runWithFixedOptParallel' params solvers c (toTree n
                          (fromPruefer (pathPruefer n) )) (edgesOfComplete n) (fes n) fsts s r
            Disj n -> compute (pp args) (ns n)
              $ \r n -> runAllDisjoint params n cpl solvers c s
            Star n -> compute (pp args) (ns n)
              $ \r n -> runWithFixedNEParallel' True params solvers c (toTree n
                          (fromPruefer (starPruefer n) )) (fes n) fsts s r
            BinTree n -> compute (pp args) (ns n)
              $ \r n -> runWithFixedNEParallel Prog.prog params solvers c
                          (binaryTreeOfHeight n)
                          (levelTreesInBinaryOfHeight n)
                          (fes n) fsts
                          s r
            Wheel n -> compute (pp args) (ns n)
              $ \r n -> run 0 (edgesOfWheel n) (canonicalSpanningTreeOfWheel n) solvers c s r
            Cube d -> compute (pp args) (ns d)
              $ \r d -> run (replicate d (0::Int)) (edgesOfHypercube d) (canonicalSpanningTreeOfHypercube d)
                solvers c s r
            FanOfFans n k -> run [0] (edgesOfFanOfFans n k) (canonicalSpanningTreeOfFanOfFans n k)
              solvers c s start
              >>= outend (pp args)
            Grid w h ->
                run (1,1) (edgesOfGrid w h) (canonicalSpanningTreeOfGrid w h) solvers c s start
                >>= outend (pp args)
            TwoPaths n -> compute (pp args) (ns n)
              $ \r n -> do
                  let opt = pathFromPerm [0,1 .. n]
                      nes = pathFromPerm . (0:) <$> L.permutations [1 .. n]
                  runWithFixedOptParallel Prog.prog params solvers c opt nes edgesInUnion
                      (\o ne -> allSpanningTreesAt 0 (edgesInUnion o ne) (init $ edges $ toChildMap o))
                      s r
        Find -> do
         case t of
           Star n -> do
              findAllFixedNE True params solvers c (toTree n (fromPruefer (starPruefer n) )) start
            >>= mapM_  (out (pp args))
           All n -> do
            findAll params solvers c n start
            >>= mapM_  (out (pp args))
    Evolution t n start keep me -> do
      let m = case me of
            "pos" -> POS
            "gnene" -> GNENE
      case t of
        Rand -> liveRand m n start keep
        Fan -> do
          start <- replicateM start $ randIndiv m n
          live m keep $ italianInstance n : start
        Ring -> do
          start <- replicateM start $ randRing n
          live m keep start
        EGrid w h -> do
          start <- replicateM start $ randGrid w h
          live m keep start
    QuasiBip i b s -> do
      let solvers = case b of
            "z3" -> [z3]
            "cvc4" -> [cvc4]
            "opensmt" -> [opensmt]
            "yices" -> [yices]
            "all" -> allsolvers
          params = Parameters {
             sharingscheme = l
             , posswitch = True
             , normalizeswitch = True
             , debugfile = Nothing
             , systemsfile = Nothing
             , completeswitch = False
            }
      case i of
        DoubleFan n -> do
          let (opt, ne, es, sts) = doubleFan n
          runOne Multicast.progQuasiBipartite params solvers opt ne es sts s 1
          >>= print
        FanSub3Fans n -> do
          let (opt, ne, es, sts) = fanSub3Fans n
          runOne Multicast.progQuasiBipartite params solvers opt ne es sts s 1
          >>= print
        Italian n -> do
          let (opt, ne, es, sts) = italianInstanceMulticast n
          runOne Multicast.progQuasiBipartite params solvers opt ne es sts s 1
          >>= print
