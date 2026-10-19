-- Parsing boundary only: both the higher-order obligations and the embedded
-- first-order CPF are checked by the Isabelle-generated combined checker.
module Main where

import qualified Higher_Order_Core as C
import qualified Higher_Order_Algebraic_Embedding as F
import qualified Higher_Order_CeTA_Check as D
import qualified Arith as A
import Control.Monad (replicateM)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.ParserCombinators.ReadP

token s = string s >> skipSpaces
number = do
  ds <- munch1 (`elem` ['0'..'9'])
  skipSpaces
  let n = read ds :: Integer
  if n <= 1000000 then return n else pfail
nat = A.nat_of_integer <$> number
items p = number >>= \n -> replicateM (fromInteger n) p
ty = (token "base " >> C.HBase <$> nat)
  <++ (token "arrow " >> C.HArrow <$> ty <*> ty)
patternTerm = (token "pbound " >> C.PBound <$> nat)
  <++ (token "pconst " >> C.PConst <$> nat)
  <++ (token "papp " >> C.PApp <$> patternTerm <*> patternTerm)
  <++ (token "pabs " >> C.PAbs <$> ty <*> patternTerm)
  <++ (token "meta " >> C.PMeta <$> nat <*> items patternTerm)
foTerm = (token "var " >> F.HFOVar <$> nat)
  <++ (token "fun " >> F.HFOFun <$> nat <*> items foTerm)

delegation = do
  token "ho-ceta-delegation "
  signature <- items ty
  rules <- items ((\g l r -> (g,(l,r))) <$> items ty <*> patternTerm <*> patternTerm)
  symbols <- items nat
  pairs <- items ((,) <$> foTerm <*> foTerm)
  ce <- nat
  ranks <- items nat
  arities <- items nat
  priorities <- items nat
  sorts <- items nat
  fuel <- nat
  eof
  return (D.ho_check_ceta_delegation_xml signature rules symbols pairs ce
    ranks arities priorities sorts fuel)

main = do
  args <- getArgs
  case args of
    [sourceFile, cpfFile] -> do
      source <- readFile sourceFile
      cpf <- readFile cpfFile
      case readP_to_S (skipSpaces >> delegation) source of
        [(check, "")] | check (A.explode cpf) -> putStrLn "CERTIFIED YES"
        _ -> putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-ho-delegation SOURCE-CERTIFICATE FIRST-ORDER-PROOF.xml" >> exitFailure
