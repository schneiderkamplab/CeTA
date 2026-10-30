-- Diagnostic trace of generated checks; never a source verdict.
module Main where
import qualified Prolog_Transfer_Generated as G
import Data.Char (ord, chr)
import System.Environment (getArgs)
main = do
  [file] <- getArgs
  input <- readFile file
  case G.parse_xml_string G.lpp_context_module_parser (map (G.char_of_integer . toInteger . ord) input) of
    G.Sumbot (G.Inr (p,(fuel,(root,(nds,(states,(contexts,(typings,((summaries,(sp,receipts)),(returned,(arity,(actions,q)))))))))))) -> do
      print ("source", G.lp_cut_source_program p)
      print ("transfer", G.lpp_check_transfer_contract summaries sp receipts)
      mapM_ (\i -> print (i,
        G.lpp_check_context_typing (G.lpp_transfer_lookup summaries) (contexts !! i) (typings !! i) (G.lpp_context_module_types (actions !! i)),
        G.lpp_check_context_module_action fuel p q nds states contexts (nds !! i) (states !! i) (contexts !! i) returned arity (actions !! i))) [0 .. length nds - 1]
      mapM_ (\i -> case actions !! i of
        G.LPPCMPrimitive (G.LPPCSPrimitive (G.LPPIRCut action)) ->
          print ("shared",i,G.lpc_check_return_action fuel p q nds states (nds !! i) (states !! i) returned arity action)
        _ -> pure ()) [0 .. length nds - 1]
    G.Sumbot (G.Inl e) -> putStrLn (map (chr . fromInteger . G.integer_of_char) e)
