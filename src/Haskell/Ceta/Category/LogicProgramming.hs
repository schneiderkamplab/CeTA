{-# LANGUAGE CPP #-}
-- Every acceptance branch is generated from Isabelle.
module Ceta.Category.LogicProgramming (run, runProlog) where
import Ceta.Input.Characters (cachedCharacters)
#ifdef LP_SEG_TRIPLES
import qualified LP_Triples_Generated as T
#endif
#ifdef LP_SEG_PROJECTED
import qualified LP_SEG_Projected_Generated as G
#endif
import qualified LP_Finite_Generated as F
import qualified LP_Cut_Projected_Generated as P
import qualified LP_Return_Module_Generated as R
import qualified LP_SEG_Certificate_Generated as S
import qualified LP_Cut_NO_Generated as N
#ifdef LP_PROLOG_STATIC
import qualified Prolog_Static_Generated as PS
#endif
#ifdef LP_PROLOG_CONTEXT
import qualified Prolog_Context_Generated as PC
#endif
#ifdef LP_PROLOG_CONTEXT_ITS
import qualified Prolog_Context_ITS_Generated as PCI
#endif
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
#ifdef LP_SEG_TRIPLES
        else if T.check_lp_triple_pidp_xml (decodeT input)
        then putStrLn "CERTIFIED LP DEPENDENCY-TRIPLE CHILD"
#endif
#ifdef LP_PROLOG_STATIC
        else if PS.check_lpc_uniform_xml (cachedCharacters PS.explode input)
        then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT NO"
#endif
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
        else if F.check_lp_finite_xml (decodeF input)
          then putStrLn "CERTIFIED FINITE-TERM LP"
        else if R.check_lp_nontermination_all_xml xml
          then putStrLn "CERTIFIED TOCL09 LP NO"
        else putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-lp-seg certificate.xml" >> exitFailure

-- Keep the existing category CLI and verdicts behind the shared dispatcher.
run :: [String] -> IO ()
run args = withArgs args main

-- Prolog has an explicit source bridge; an LP child alone is insufficient.
runProlog :: [String] -> IO ()
runProlog [path] = do
  input <- readFile path
#ifdef LP_PROLOG_STATIC
  if PS.check_lpp_static_xml (cachedCharacters PS.explode input) ||
    PS.check_lpp_undefined_xml (cachedCharacters PS.explode input)
    then putStrLn "CERTIFIED SOURCE-BOUND STATIC PROLOG"
    else if
#ifdef LP_PROLOG_CONTEXT
#ifdef LP_PROLOG_CONTEXT_ITS
      PCI.check_lpp_context_its_xml (cachedCharacters PCI.explode input) ||
#endif
      PC.check_lpp_established_finite_triples_xml (cachedCharacters PC.explode input) ||
      PC.check_lpp_established_triples_xml (cachedCharacters PC.explode input) ||
      PC.check_lpp_context_composed_certificate_xml (cachedCharacters PC.explode input) ||
      PC.check_lpp_context_certificate_xml (cachedCharacters PC.explode input) ||
#endif
      PS.check_lpp_return_triples_xml (cachedCharacters PS.explode input) ||
      PS.check_lpp_module_triples_xml (cachedCharacters PS.explode input)
      then putStrLn "CERTIFIED SOURCE-BOUND PROLOG"
    else if PS.check_lpp_test_no_xml (cachedCharacters PS.explode input) ||
      PS.check_lpp_integer_no_xml (cachedCharacters PS.explode input)
      then putStrLn "CERTIFIED SOURCE-BOUND PROLOG NO"
    else if PS.check_lpp_static_no_xml (cachedCharacters PS.explode input) ||
      PS.check_lpp_uniform_xml (cachedCharacters PS.explode input)
      then putStrLn "CERTIFIED SOURCE-BOUND STATIC PROLOG NO"
      else putStrLn "REJECTED" >> exitFailure
#else
  putStrLn "UNSUPPORTED" >> exitFailure
#endif
runProlog _ = putStrLn "usage: ceta --category prolog certificate.xml" >> exitFailure

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

decodeF = cachedCharacters F.explode
