-- Acceptance is exclusively the Isabelle-generated ITS checker.
module Ceta.Category.ITS (run) where
import qualified ITS_Checker as C
import Data.Char (ord, chr)
import System.Exit (exitFailure)

run :: [String] -> IO ()
run [path] = check C.check_its5_string path
run ["--legacy", path] = check C.check_its4_string path
run _ = putStrLn "usage: ceta --category its [--legacy] CERTIFICATE.xml" >> exitFailure

check checker path = do
  source <- readFile path
  case checker (map (C.char_of_integer . toInteger . ord) source) of
    C.Inr () -> putStrLn "CERTIFIED"
    C.Inl message -> do
      putStrLn (map (chr . fromInteger . C.integer_of_char) message)
      exitFailure
