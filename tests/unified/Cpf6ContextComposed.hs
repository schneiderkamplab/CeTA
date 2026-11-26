-- CPF transport only; mathematical validity belongs to the generated checker.
import qualified Ceta.Input.Cpf6 as C
import System.Exit (die)
import System.Environment (getArgs)
import Data.List (isPrefixOf)
replace old new [] = []
replace old new s | old `isPrefixOf` s = new ++ replace old new (drop (length old) s)
replace old new (x:xs) = x : replace old new xs
main = do
 [path] <- getArgs
 source <- readFile path
 case C.prologCertificate source of
  Left e -> die e
  Right native -> case C.prologCertificate native of
   Right same | same == native -> putStrLn "contextual native transport stable"
   _ -> die "native contextual transport changed"

 mapM_ (\(old,new) -> do
   if not (old `contains` source) then die ("missing mutation target: " ++ old) else return ()
   case C.prologCertificate (replace old new source) of
    Left _ -> return ()
    Right _ -> die ("invalid transport accepted: " ++ old))
   [("<yes/>","<no/>"),("<cpfVersion>6.0</cpfVersion>","<cpfVersion>5.0</cpfVersion>"),
    ("<typings><facts/><facts/><facts/></typings>",""),
    ("</prologContextComposedDependencyTriplesProof>","<extra/></prologContextComposedDependencyTriplesProof>")]
 putStrLn "contextual transport mutation checks passed"
contains needle [] = False
contains needle s@(_:rest) = needle `isPrefixOf` s || contains needle rest
