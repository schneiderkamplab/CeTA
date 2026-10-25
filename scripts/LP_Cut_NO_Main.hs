-- The additional NO acceptance branch is entirely generated from Isabelle.
module Main where
import qualified LP_Return_Module_Generated as R
import qualified LP_SEG_Certificate_Generated as S
import qualified LP_Cut_NO_Generated as N
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      input <- readFile path
      let xml = R.explode input
      if N.check_lpc_no_xml (N.explode input)
        then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT NO"
        else if S.check_lpc_seg_free_certificate_xml (S.explode input) ||
                S.check_lpc_seg_certificate_xml (S.explode input) ||
                R.check_lpc_return_nested_constructor_xml xml ||
                R.check_lpc_return_composed_constructor_xml xml ||
                R.check_lpc_return_module_constructor_xml xml ||
                R.check_lpc_return_constructor_xml xml || R.check_lpc_xml xml ||
                R.check_lpc_constructor_xml xml || R.check_lpc_mgu_constructor_xml xml
          then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT"
        else if R.check_lp_constructor_any_xml xml
          then putStrLn "CERTIFIED TOCL09 LP"
        else if R.check_lp_nontermination_all_xml xml
          then putStrLn "CERTIFIED TOCL09 LP NO"
        else putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-lp-seg certificate.xml" >> exitFailure
