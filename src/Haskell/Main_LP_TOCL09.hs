-- The verified bridge permits infinite runtime trees and binds the program,
-- query groundness pattern and reconstructed continuation translation.
module Main where
import qualified LP_TOCL09_Generated as C
import System.Environment (getArgs)
import System.Exit (exitFailure)

main = do
  args <- getArgs
  case args of
    [path] -> do
      text <- readFile path
      if C.check_lp_seg_full_xml (C.explode text)
        then putStrLn "CERTIFIED TOCL09 LP"
        else if C.check_lp_nontermination_xml (C.explode text)
          then putStrLn "CERTIFIED TOCL09 LP NO"
          else putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-lp-tocl09 CERTIFICATE" >> exitFailure
