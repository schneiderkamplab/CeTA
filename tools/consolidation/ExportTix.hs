module Main where
import Trace.Hpc.Tix
import System.Environment (getArgs)
import Data.List (intercalate)
main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      parsed <- readTix path
      case parsed of
        Nothing -> fail "cannot parse HPC tix"
        Just (Tix modules) -> mapM_ output modules
    _ -> fail "usage: export-tix FILE"
  where
    output (TixModule name hash count ticks) =
      putStrLn (intercalate "\t" [name, show hash, show count, intercalate "," [show i | (i,t) <- zip [0::Int ..] ticks, t > 0]])
