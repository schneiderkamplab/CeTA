-- Local source-node checks against the unmodified Isabelle-generated checker.
-- These are not complete source termination certificates.
module Main where
import qualified Prolog_Transfer_Generated as G
import Data.Char (chr)
import Control.Monad (forM_, unless)
checks = G.lpp_integer_node_regressions ++ G.lpp_integer_action_regressions
  ++ G.lpp_context_node_regressions ++ G.lpp_context_arithmetic_regressions
  ++ G.lpp_context_graph_regressions ++ G.lpp_context_staged_regressions
main :: IO ()
main = do
  forM_ checks $ \(encoded, accepted) -> do
    let name = map (chr . fromInteger . G.integer_of_char) encoded
    unless accepted (error name)
    putStrLn ("PASS " ++ name)
  putStrLn (show (length checks) ++ " local source-node checks passed; no source verdict")
