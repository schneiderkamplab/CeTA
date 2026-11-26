-- Transport only: this program does not establish any mathematical verdict.
import qualified Ceta.Input.Cpf6 as C
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Control.Monad (forM_)
main = do
  paths <- getArgs
  forM_ paths $ \path -> do
    source <- readFile path
    case C.prologCertificate source of
      Left message -> putStrLn (path ++ ": " ++ message) >> exitFailure
      Right native -> writeFile (path ++ ".decoded") native
