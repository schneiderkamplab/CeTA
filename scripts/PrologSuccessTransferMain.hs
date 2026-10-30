module Main where
import qualified Prolog_Transfer_Generated as G
import Data.Char (ord)
import System.Environment (getArgs)
import System.Exit (exitFailure)
main = do
  [file] <- getArgs
  input <- readFile file
  if G.check_lpp_success_transfer_xml (map (G.char_of_integer . toInteger . ord) input)
    then putStrLn "VALID CONDITIONAL CONTRACT"
    else putStrLn "REJECTED" >> exitFailure
