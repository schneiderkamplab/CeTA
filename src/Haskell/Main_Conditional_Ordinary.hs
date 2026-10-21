-- Parsing and invocation only; the original CTRS and its erasure proof are
-- checked together by the Isabelle-generated function.
module Main where
import qualified Conditional_Erasure_Generated as C
import System.Environment (getArgs)
import System.Exit (exitFailure)

main = do
  args <- getArgs
  case args of
    [path] -> do
      text <- readFile path
      if C.check_conditional_erasure_xml (C.explode text)
        then putStrLn "CERTIFIED"
        else putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-conditional-erasure CERTIFICATE" >> exitFailure
