-- Acceptance comes only from the Isabelle-generated source-bound checker.
module Main where
import qualified LP_Cut_Generated as C
import System.Environment (getArgs)
import System.Exit (exitFailure)

main = do
  args <- getArgs
  case args of
    ["--diagnose", path] -> do
      text <- readFile path
      print (C.lpc_xml_diagnostics (C.explode text))
    [path] -> do
      text <- readFile path
      if C.check_lpc_xml (C.explode text) || C.check_lpc_constructor_xml (C.explode text)
          || C.check_lpc_mgu_constructor_xml (C.explode text)
        then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT"
        else if C.check_lp_constructor_any_xml (C.explode text)
          then putStrLn "CERTIFIED TOCL09 LP"
          else if C.check_lp_nontermination_all_xml (C.explode text)
            then putStrLn "CERTIFIED TOCL09 LP NO"
            else putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-lp-cut [--diagnose] CERTIFICATE" >> exitFailure
