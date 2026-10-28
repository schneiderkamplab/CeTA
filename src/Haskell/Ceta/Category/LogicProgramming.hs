{-# LANGUAGE CPP #-}
-- Every acceptance branch is generated from Isabelle.
module Ceta.Category.LogicProgramming (run) where
import Ceta.Input.Characters (cachedCharacters)
#ifdef LP_SEG_TRIPLES
import qualified LP_Triples_Generated as T
#endif
#ifdef LP_SEG_PROJECTED
import qualified LP_SEG_Projected_Generated as G
#endif
import qualified LP_Cut_Projected_Generated as P
import qualified LP_Return_Module_Generated as R
import qualified LP_SEG_Certificate_Generated as S
import qualified LP_Cut_NO_Generated as N
import System.Environment (getArgs, withArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      input <- readFile path
      let xml = decodeR input
      if
#ifdef LP_SEG_TRIPLES
        T.check_lpc_return_triples_xml (decodeT input) ||
        T.check_lpc_return_nested_triples_xml (decodeT input) ||
        T.check_lpc_return_composed_triples_xml (decodeT input) ||
        T.check_lpc_return_module_triples_xml (decodeT input) ||
        T.check_lpc_seg_triples_xml (decodeT input) ||
#endif
#ifdef LP_SEG_PROJECTED
        G.check_lpc_seg_projected_certificate_xml (decodeG input) ||
#endif
        P.check_lpc_projected_xml (decodeP input)
        then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT"
        else if N.check_lpc_no_xml (decodeN input)
        then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT NO"
        else if S.check_lpc_seg_free_certificate_xml (decodeS input) ||
                S.check_lpc_seg_certificate_xml (decodeS input) ||
                R.check_lpc_return_nested_constructor_xml xml ||
                R.check_lpc_return_composed_constructor_xml xml ||
                R.check_lpc_return_module_constructor_xml xml ||
                R.check_lpc_return_constructor_xml xml || R.check_lpc_xml xml ||
                R.check_lpc_constructor_xml xml || R.check_lpc_mgu_constructor_xml xml
          then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT"
#ifdef LP_SEG_TRIPLES
        else if T.check_lp_initial_triples_xml (decodeT input)
          then putStrLn "CERTIFIED TOCL09 LP"
#endif
        else if R.check_lp_constructor_any_xml xml
          then putStrLn "CERTIFIED TOCL09 LP"
        else if R.check_lp_nontermination_all_xml xml
          then putStrLn "CERTIFIED TOCL09 LP NO"
        else putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-lp-seg certificate.xml" >> exitFailure

-- Keep the existing category CLI and verdicts behind the shared dispatcher.
run :: [String] -> IO ()
run args = withArgs args main

#ifdef LP_SEG_TRIPLES
decodeT = cachedCharacters T.explode
#endif

#ifdef LP_SEG_PROJECTED
decodeG = cachedCharacters G.explode
#endif

decodeP = cachedCharacters P.explode

decodeR = cachedCharacters R.explode

decodeS = cachedCharacters S.explode

decodeN = cachedCharacters N.explode
