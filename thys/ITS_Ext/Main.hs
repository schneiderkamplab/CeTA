module Main where
import qualified Ceta.Category.ITS as ITS
import System.Environment (getArgs)
main :: IO ()
main = getArgs >>= ITS.run
