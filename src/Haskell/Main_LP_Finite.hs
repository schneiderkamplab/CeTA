-- The generated checker rebuilds the translation from the source clauses and
-- checks its child proof. This entry point claims finite-term LD semantics only.
module Main where
import qualified LP_Finite_Generated as C
import System.Environment (getArgs)
import System.Exit (exitFailure)

main = do
  args <- getArgs
  case args of
    [path] -> do
      text <- readFile path
      if C.check_lp_finite_xml (C.explode text)
        then putStrLn "CERTIFIED FINITE-TERM LP"
        else putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-lp-finite CERTIFICATE" >> exitFailure
