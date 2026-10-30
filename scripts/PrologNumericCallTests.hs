module Main where
import qualified Prolog_Numeric_Calls_Generated as G
import Data.Char (chr)
import Control.Monad (forM_, unless)
main :: IO ()
main = do
  forM_ G.lpp_numeric_call_regressions $ \(encoded, accepted) -> do
    let label = map (chr . fromInteger . G.integer_of_char) encoded
    unless accepted (error label)
    putStrLn ("PASS " ++ label)
  putStrLn (show (length G.lpp_numeric_call_regressions) ++ " numeric component checks; no source verdict")
