-- All acceptance functions below are generated from proved Isabelle checkers.
-- A generic triples result is not a source-program termination verdict.
module Main where
import qualified LP_Triples_Generated as T
import System.Environment (getArgs)
import System.Exit (exitFailure)
main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      input <- readFile path
      let xml = T.explode input
      if T.check_lpc_return_triples_xml xml || T.check_lpc_return_nested_triples_xml xml
          || T.check_lpc_return_composed_triples_xml xml || T.check_lpc_return_module_triples_xml xml
          || T.check_lpc_seg_triples_xml xml
        then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT"
        else if T.check_lp_initial_triples_xml xml
          then putStrLn "CERTIFIED TOCL09 LP"
        else putStrLn "REJECTED" >> exitFailure
    ["--triples-only", path] -> do
      input <- readFile path
      if T.check_lp_triple_pidp_xml (T.explode input)
        then putStrLn "CERTIFIED DEPENDENCY TRIPLES (NOT A SOURCE VERDICT)"
        else putStrLn "REJECTED" >> exitFailure
    ["--diagnostic", path] -> do
      input <- readFile path
      print (T.lpc_seg_triples_diagnostics_xml (T.explode input))
    _ -> putStrLn "usage: ceta-lp-triples [--triples-only] certificate.xml" >> exitFailure
