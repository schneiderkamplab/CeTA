module Main where
import qualified LP_Cut_Projected_Generated as P
import System.Environment (getArgs)
import System.Exit (exitFailure)
main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      input <- readFile path
      if P.check_lpc_projected_xml (P.explode input)
        then putStrLn "CERTIFIED SOURCE-BOUND LP WITH CUT"
        else putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-lp-projected certificate.xml" >> exitFailure
