-- Diagnostic only: reports generated checker predicates, never accepts a proof.
module LP_Cut_SEG_Diagnostic where
import qualified LP_SEG_Certificate_Generated as S
import System.Environment (getArgs)

main :: IO ()
main = do
  [path] <- getArgs
  input <- readFile path
  S.case_sum_bot (putStrLn "parser: bottom") (\_ -> putStrLn "parser: error")
    (\(p,(q,(modes,(fuel,(roots,(fs,(regions,(continuations,(controls,(dataMap,(fallback,(constructors,(rules,proof))))))))))))) -> do
      let ic f = f `elem` continuations
          c = S.lpc_lookup fallback controls
          d = S.lpc_lookup fallback dataMap
          cs = S.set constructors
          rs = S.set rules
      putStrLn $ "full: " ++ show (S.check_lpc_seg_free_certificate S.tp_rbt_impl S.dpp_rbt_impl fuel p roots fs regions q modes continuations controls dataMap fallback constructors rules proof)
      mapM_ (\(i,component) -> do
        putStrLn $ "component " ++ show i ++ ": " ++ show (S.lpc_seg_free_check_component fuel p roots fs (roots!!i) (fs!!i) ic c d cs rs component)
        case component of
          S.LPCSEGFreeRegion region localFree -> do
            let control=S.lpcsg_control region
                ns=S.lpcsc_nodes control
                states=S.lpcsc_states control
                program=S.lpcsc_program control
            putStrLn $ "  control: " ++ show (S.lpc_seg_free_control_data_check fuel p control localFree)
            mapM_ (\(j,action) -> case action of
              Nothing -> pure ()
              Just act -> if S.lpc_check_return_free_module_action fuel p program ns states localFree (ns!!j) (localFree!!j) (states!!j) (S.lpcsc_returned control) (S.lpcsc_arity control) act
                then pure () else putStrLn $ "  rejected action " ++ show j)
              (zip [0..] (S.lpcsc_actions control))
          _ -> pure ()) (zip [0..] regions))
    (S.parse_xml_string S.lpc_seg_free_certificate_parser (S.explode input))
