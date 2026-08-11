module Main (main) where

import Ceta_Relative
import System.Environment (getArgs)
import System.Exit (ExitCode(..), exitWith)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> readFile path >>= certify
    _ -> do
      hPutStrLn stderr "usage: ceta-relative-adp certificate.cpf.xml"
      exitWith (ExitFailure 4)

certify :: String -> IO ()
certify cpf =
  case certify_proof_integrated False Nothing Nothing Nothing (explode cpf) of
    Certified -> putStrLn "CERTIFIED"
    Error message -> do
      putStrLn "REJECTED"
      hPutStrLn stderr message
      exitWith (ExitFailure 1)
    Unsupported message -> do
      putStrLn "UNSUPPORTED"
      hPutStrLn stderr message
      exitWith (ExitFailure 2)
