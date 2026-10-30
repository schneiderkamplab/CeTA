-- Conditional source-to-ITS guard receipt checker, not a source-root verdict.
module Main where
import qualified Prolog_Transfer_Generated as G
import Data.Char (ord)
import System.Environment (getArgs)
import System.Exit (exitFailure)
main :: IO ()
main = do
  [file] <- getArgs
  input <- readFile file
  if G.check_lpp_numeric_row_guard_xml (map (G.char_of_integer . toInteger . ord) input)
    then putStrLn "VALID NUMERIC GUARD CORRESPONDENCE"
    else putStrLn "REJECTED" >> exitFailure
