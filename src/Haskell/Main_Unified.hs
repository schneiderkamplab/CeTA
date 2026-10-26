-- Category selection only. Acceptance remains in the Isabelle-generated checkers.
module Main (main) where
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import qualified Ceta.Category.Rewriting as Rewriting
import qualified Ceta.Category.Cycle as Cycle
import qualified Ceta.Category.Conditional as Conditional
import qualified Ceta.Category.ConditionalErasure as ConditionalErasure
import qualified Ceta.Category.LogicProgramming as LogicProgramming
import qualified Ceta.Category.HigherOrder as HigherOrder
import qualified Ceta.Category.HigherOrderDelegation as HigherOrderDelegation

main :: IO ()
main = getArgs >>= dispatch

dispatch :: [String] -> IO ()
dispatch ["--list-categories"] = mapM_ putStrLn categories
dispatch ("--category" : category : args) = case category of
  "cpf" -> Rewriting.run args
  "cycle" -> Cycle.run args
  "conditional" -> Conditional.run args
  "conditional-erasure" -> ConditionalErasure.run args
  "lp" -> LogicProgramming.run args
  "higher-order" -> HigherOrder.run args
  "higher-order-delegation" -> HigherOrderDelegation.run args
  _ -> hPutStrLn stderr ("Unknown certificate category: " ++ category) >> exitFailure
dispatch ["--category"] = hPutStrLn stderr "Missing category; use --list-categories" >> exitFailure
dispatch args = Rewriting.run args

categories :: [String]
categories = ["cpf", "cycle", "conditional", "conditional-erasure", "lp", "higher-order", "higher-order-delegation"]
