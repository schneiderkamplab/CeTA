-- Correspondence checks against the unmodified generated component checker.
-- Acceptance means the source guard and ITS formula match, not that a source
-- program terminates or even that the guard is satisfiable.
module Main where
import qualified Prolog_Transfer_Generated as G
import Control.Monad (unless)

c :: Integer -> G.Lpp_integer_expression Integer
c = G.LPPEConstant . G.Int_of_integer
assert name yes = unless yes (error name)
check k comparison a b f = G.lpp_check_numeric_guard k comparison
  (G.lpp_expression_term a) (G.lpp_expression_term b) a b f
formula comparison a b = G.lpp_comparison_its comparison
  (G.lpp_expression_its a) (G.lpp_expression_its b)
main :: IO ()
main = do
  let x = G.LPPEVariable 0
      rhs = G.LPPESubtract x (c 1)
      quotient = G.LPPEDivide (c (10^100)) (G.Int_of_integer (-3))
      nested = G.LPPEAdd quotient (G.LPPEModulo (c 7) (G.Int_of_integer (-3)))
      good op a b = check [0] op a b (formula op a b)
  assert "strict guard" (good G.LPPIntLess (c 0) x)
  assert "weak guard" (good G.LPPIntLessEqual (c 0) x)
  assert "evaluation equality" (good G.LPPIntEqual x rhs)
  assert "disequality" (good G.LPPIntNotEqual x (c 0))
  assert "nested huge signed division" (good G.LPPIntEqual x nested)
  assert "lost integer premise" (not (check [] G.LPPIntLess (c 0) x (formula G.LPPIntLess (c 0) x)))
  assert "changed comparator" (not (check [0] G.LPPIntLess (c 0) x (formula G.LPPIntLessEqual (c 0) x)))
  assert "swapped operands" (not (check [0] G.LPPIntLess (c 0) x (formula G.LPPIntLess x (c 0))))
  assert "changed evaluated source" (not (G.lpp_check_numeric_guard [0] G.LPPIntEqual
    (G.lpp_expression_term x) (G.lpp_expression_term (c 1)) x rhs (formula G.LPPIntEqual x rhs)))
  let zero = G.LPPEDivide x (G.Int_of_integer 0)
  assert "zero divisor" (not (good G.LPPIntEqual x zero))
  putStrLn "10 numeric guard correspondence checks passed (5 positive, 5 negative); no source verdict"
