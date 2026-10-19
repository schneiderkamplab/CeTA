-- Parsing/CLI boundary only. All mathematical acceptance is delegated to the
-- Isabelle-generated Higher_Order_Checker module. Numbers are nonnegative;
-- unknown tokens, trailing data and malformed lists are rejected.
module Main where

import qualified Higher_Order_Checker as C
import Control.Monad (replicateM)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.ParserCombinators.ReadP

token :: String -> ReadP ()
token s = string s >> skipSpaces

number :: ReadP Integer
number = do
  ds <- munch1 (`elem` ['0'..'9'])
  skipSpaces
  let n = read ds
  if n <= 1000000 then return n else pfail

nat :: ReadP C.Nat
nat = C.nat_of_integer <$> number

items :: ReadP a -> ReadP [a]
items parser = do
  n <- number
  replicateM (fromInteger n) parser

ty :: ReadP C.Ho_type
ty = (token "base " >> C.HBase <$> nat)
  <++ (token "arrow " >> C.HArrow <$> ty <*> ty)

term :: ReadP C.Ho_term
term = (token "bound " >> C.HBound <$> nat)
  <++ (token "free " >> C.HFree <$> nat)
  <++ (token "const " >> C.HConst <$> nat)
  <++ (token "app " >> C.HApp <$> term <*> term)
  <++ (token "abs " >> C.HAbs <$> ty <*> term)

patternTerm :: ReadP C.Ho_pattern
patternTerm = (token "pbound " >> C.PBound <$> nat)
  <++ (token "pconst " >> C.PConst <$> nat)
  <++ (token "papp " >> C.PApp <$> patternTerm <*> patternTerm)
  <++ (token "pabs " >> C.PAbs <$> ty <*> patternTerm)
  <++ (token "meta " >> C.PMeta <$> nat <*> items patternTerm)

step :: ReadP C.Ho_step_proof
step = (token "rule " >> C.HRule <$> nat <*> items term)
  <++ (token "beta " >> return C.HBeta)
  <++ (token "left " >> C.HLeft <$> step)
  <++ (token "right " >> C.HRight <$> step)
  <++ (token "under " >> C.HUnder <$> step)

context :: ReadP C.Ho_context
context = (token "hole " >> return C.HHole)
  <++ (token "cleft " >> C.HCLeft <$> context <*> term)
  <++ (token "cright " >> C.HCRight <$> term <*> context)

check :: ReadP Bool
check = pump <++ path

pump :: ReadP Bool
pump = do
  token "ho-pump "
  signature <- items ty
  rules <- items ((\g l r -> (g, (l,r))) <$> items ty <*> patternTerm <*> patternTerm)
  index <- nat
  substitution <- items term
  eof
  return (C.ho_check_rule_pump signature rules index substitution)

path :: ReadP Bool
path = do
  embedding <- (token "ho-loop " >> return False)
    <++ (token "ho-embedding " >> return True)
  signature <- items ty
  variables <- items ty
  rules <- items ((\g l r -> (g, (l,r))) <$> items ty <*> patternTerm <*> patternTerm)
  rootType <- ty
  start <- term
  steps <- items step
  ctxt <- if embedding then context else return C.HHole
  eof
  return (if embedding then C.ho_check_embedding signature variables rules rootType start steps ctxt
          else C.ho_check_loop signature variables rules rootType start steps)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      source <- readFile path
      case readP_to_S (skipSpaces >> check) source of
        [(True, "")] -> putStrLn "CERTIFIED HO LOOP"
        _ -> putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "Usage: ceta-higher-order CAPSULE" >> exitFailure
