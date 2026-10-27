module Main where
import Ceta.Input.Characters (cachedCharacters)
import qualified Ceta_Relative as C
import Data.Char (chr)
import Control.Exception (SomeException, evaluate, try, displayException)
import Control.Monad (unless)

old = C.explode
new = cachedCharacters C.explode
force xs = evaluate (sum [if c == c then 1 else 0 | c <- xs] :: Integer)
main = do
  let samples = [map chr [0..127], reverse (map chr [0..127]), concat (replicate 64 "<tag> \t\ntext</tag>"), ""]
  mapM_ (\s -> unless (old s == new s) (error "ASCII conversion differs")) samples
  mapM_ (\s -> do
    a <- try (force (old s)) :: IO (Either SomeException Integer)
    b <- try (force (new s)) :: IO (Either SomeException Integer)
    case (a,b) of
      (Left x,Left y) -> unless (takeWhile (/='\n') (displayException x)==takeWhile (/='\n') (displayException y)) (error "exception differs")
      _ -> error "non-ASCII boundary changed") ["\128", "a\255", "\955", "<name>\128512</name>"]
  putStrLn "All ASCII characters and non-ASCII rejection behavior agree with the generated decoder."
