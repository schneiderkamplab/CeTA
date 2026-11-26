-- Parsing/routing guards only; mathematical acceptance is tested separately.
import qualified Ceta.Input.Cpf6 as C
import System.Exit (die)
import System.Environment (getArgs)
main = do
 legacy <- readFile "tests/unified/lp-finite.xml"
 args <- getArgs
 cpf <- case args of [path] -> readFile path; _ -> die "usage: Cpf6Routing.hs CPF6.xml"
 let wrappers = ["", "<!-- comment -->\n", "<?xml version=\"1.0\"?>\n<!-- comment -->\n"]
 mapM_ (\p -> if C.logicProgramming (p ++ legacy) == Right (p ++ legacy) then return () else die "legacy routing changed bytes") wrappers
 mapM_ (\p -> case C.logicProgramming (p ++ cpf) of Right _ -> return (); Left e -> die e) wrappers
 case C.logicProgramming "<certificationProblem><invalid/></certificationProblem>" of
  Left _ -> putStrLn "7 CPF6 routing guards passed"
  Right _ -> die "malformed CPF envelope bypassed validation"
