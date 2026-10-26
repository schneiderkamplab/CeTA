module Main where
import qualified ITS_Checker as C
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Data.Char (ord, chr)
main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      source <- readFile path
      case C.check_its4_string (map (C.char_of_integer . toInteger . ord) source) of
        C.Inr () -> putStrLn "CERTIFIED"
        C.Inl message -> do
          putStrLn (map (chr . fromInteger . C.integer_of_char) message)
          exitFailure
    _ -> putStrLn "usage: ceta-its CERTIFICATE.xml" >> exitFailure
