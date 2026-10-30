-- Residual component diagnostic; this never certifies a Prolog source root.
module Main where
import qualified Prolog_Numeric_Component_Generated as G
import Data.Char (ord)
import System.Environment (getArgs)
import System.Exit (exitFailure)
main :: IO ()
main = do
  [file] <- getArgs
  input <- readFile file
  let encoded = map (G.char_of_integer . toInteger . ord) input
  if G.check_lpp_numeric_component_xml encoded
    then putStrLn "VALID NUMERIC COMPONENT; NO SOURCE VERDICT"
    else putStrLn "REJECTED" >> exitFailure
