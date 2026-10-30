-- Local source-node checks against the unmodified Isabelle-generated checker.
-- These are not complete source termination certificates.
module Main where
import qualified Prolog_Transfer_Generated as G
import Data.Char (chr)
import Control.Monad (forM_, unless)
main :: IO ()
main = do
  forM_ (G.lpp_integer_node_regressions ++ G.lpp_integer_action_regressions) $ \(encoded, accepted) -> do
    let name = map (chr . fromInteger . G.integer_of_char) encoded
    unless accepted (error name)
    putStrLn ("PASS " ++ name)
  putStrLn (show (length (G.lpp_integer_node_regressions ++ G.lpp_integer_action_regressions)) ++ " local source-node checks passed; no source verdict")
