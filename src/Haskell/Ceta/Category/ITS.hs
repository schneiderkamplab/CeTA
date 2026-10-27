-- Acceptance is exclusively the Isabelle-generated ITS checker.
module Ceta.Category.ITS (run) where
import qualified ITS_Checker as C
import Data.Char (ord, chr)
import System.Exit (exitFailure)

run :: [String] -> IO ()
run [path] = do
  source <- readFile path
  case C.check_its4_string (map (C.char_of_integer . toInteger . ord) source) of
    C.Inr () -> putStrLn "CERTIFIED"
    C.Inl message -> do
      putStrLn (map (chr . fromInteger . C.integer_of_char) message)
      exitFailure
run _ = putStrLn "usage: ceta --category its CERTIFICATE.xml" >> exitFailure
