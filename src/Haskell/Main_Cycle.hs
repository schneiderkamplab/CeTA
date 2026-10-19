-- Cycle-specific front end for the Isabelle-generated checker.
-- The explicit constructors fix the claimed relation to cycle rewriting.
-- This is a native cycle certificate format, not ordinary SRS CPF.
module Main (main) where

import Prelude hiding (Word)
import qualified Cycle_Checker as C
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Read (readMaybe)

type Word = [Integer]
type Rules = [(Word,Word)]
type Steps = [(Integer,Integer)]
data Certificate
  = CycleTransport Rules Word Steps Word Word Integer Integer Word Bool
  | CycleEmbedding Rules Word Steps Word Word
  | CycleMorphism Rules Word [Word] [[Integer]] [Steps] [Integer] Bool
  deriving Read

nonnegative :: Rules -> Word -> Steps -> Bool
nonnegative rs w ss = all (>=0) (w ++ concatMap (\(l,r)->l++r) rs ++ concatMap (\(i,k)->[i,k]) ss)

check :: Certificate -> Bool
check (CycleTransport rs w ss u v p s ext right) =
  nonnegative rs w ss && all (>=0) (u++v++ext++[p,s]) &&
    C.check_cycle_transport rs w (map (\(i,k)->(C.cycle_nat i,C.cycle_nat k)) ss)
      u v (C.cycle_nat p) (C.cycle_nat s) ext right
check (CycleEmbedding rs w ss l r) =
  nonnegative rs w ss && all (>=0) (l++r) &&
    C.check_cycle_embedding rs w (map (\(i,k)->(C.cycle_nat i,C.cycle_nat k)) ss) l r
check (CycleMorphism rs pivot alphabet images traces marked mirrored) =
  all (>=0) (pivot ++ concat alphabet ++ concat images ++ marked) &&
    all (nonnegative rs []) traces &&
    C.check_cycle_morphism_direction rs pivot alphabet
      (map (map C.cycle_nat) images)
      (map (map (\(i,k)->(C.cycle_nat i,C.cycle_nat k))) traces)
      (map C.cycle_nat marked) mirrored

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      text <- readFile path
      case readMaybe text of
        Just certificate | check certificate -> putStrLn "CERTIFIED"
        _ -> putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-cycle CYCLE-CERTIFICATE" >> exitFailure
