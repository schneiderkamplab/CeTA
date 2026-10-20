-- Non-accepting diagnostics only; never used for certification.
module Diagnostic where
import qualified Main as P
import qualified Higher_Order_Checker as C
import System.Environment (getArgs)
import Text.ParserCombinators.ReadP

diagnostic :: ReadP [Bool]
diagnostic = do
  P.token "ho-call-expansion-termination "
  signature <- P.items P.ty
  rules <- P.items ((\g l r -> (g, (l,r))) <$> P.items P.ty <*> P.patternTerm <*> P.patternTerm)
  definitions <- P.items ((P.token "none " >> return Nothing)
    <++ (P.token "some " >> Just <$> ((,) <$> P.term <*> P.nat)))
  expansionFuel <- P.nat
  ordinary <- P.items P.polynomial
  marked <- P.items P.polynomial
  orderFuel <- P.nat
  ranks <- P.items P.nat
  arities <- P.items P.nat
  priorities <- P.items P.nat
  sorts <- P.items P.nat
  closureFuel <- P.nat
  eof
  return (C.ho_expansion_diagnostics signature rules definitions expansionFuel
    ordinary marked orderFuel ranks arities priorities sorts closureFuel)

main :: IO ()
main = do
  [file] <- getArgs
  input <- readFile file
  print (readP_to_S diagnostic input)
