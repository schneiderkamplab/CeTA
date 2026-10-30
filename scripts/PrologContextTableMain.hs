-- Diagnostic source-context table check; residual proof is still required.
module Main where
import qualified Prolog_Transfer_Generated as G
import Data.Char (ord)
import System.Environment (getArgs)
import System.Exit (exitFailure)
main :: IO ()
main = do
  [file] <- getArgs
  input <- readFile file
  let encoded = map (G.char_of_integer . toInteger . ord) input
  if G.check_lpp_context_table_xml encoded || G.check_lpp_context_module_xml encoded
    then putStrLn "VALID SOURCE CONTEXT TABLE; NO SOURCE VERDICT"
    else putStrLn "REJECTED" >> exitFailure
