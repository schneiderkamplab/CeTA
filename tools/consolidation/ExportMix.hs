module Main where
import Trace.Hpc.Mix
import Trace.Hpc.Util (fromHpcPos)
import System.Environment (getArgs)
import System.Directory (listDirectory)
import System.FilePath (takeExtension, dropExtension)
import Data.List (sort, intercalate)
main :: IO ()
main = do
  args <- getArgs
  case args of
    [directory] -> do
      names <- listDirectory directory
      mapM_ (output directory . dropExtension) (sort (filter ((== ".mix") . takeExtension) names))
    _ -> fail "usage: export-mix DIRECTORY"
  where
    output directory name = do
      Mix source _ hash _ entries <- readMix [directory] (Left name)
      mapM_ (\(i,(pos,label)) -> putStrLn (intercalate "\t" [name,show hash,show i,source,show (fromHpcPos pos),show label])) (zip [0::Int ..] entries)
