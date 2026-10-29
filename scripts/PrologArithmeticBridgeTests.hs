-- Component checks against unmodified Isabelle-generated code. These are not
-- Prolog root certificates and must never be counted as source YES results.
module Main where
import qualified Prolog_Arithmetic_Generated as G
import Control.Monad (unless)
import Data.Char (ord)

c :: Integer -> G.Lpp_integer_expression Integer
c = G.LPPEConstant . G.Int_of_integer
its :: Integer -> G.Term G.Ia4_sig (Integer,G.Ty)
its n = G.Fun (G.IA4_Base (G.ConstF (G.Int_of_integer n))) []
neg x = G.Fun (G.IA4_Base (G.ProdF (G.Nat 2))) [its (-1),x]
check k e = G.lpp_check_expression_bridge k (G.lpp_expression_term e) e (G.lpp_expression_its e)
assert name yes = unless yes (error name)
main :: IO ()
main = do
  let d = G.LPPEDivide (c 7) (G.Int_of_integer (-3))
      m = G.LPPEModulo (c 7) (G.Int_of_integer (-3))
      v = G.LPPESubtract (G.LPPEVariable 0) (c 1)
      huge = G.LPPEMultiply (G.LPPEPositive (c (10^100))) (G.LPPENegate (c 7))
      nested = G.LPPEAdd huge (G.LPPEModulo d (G.Int_of_integer 5))
      exact e t = G.lpp_check_expression_bridge [] (G.lpp_expression_term e) e t
  assert "negative div" (exact d (G.Fun G.IA4_Div [neg (its 7),its 3]))
  assert "negative mod" (exact m (neg (G.Fun G.IA4_Mod [neg (its 7),its 3])))
  assert "huge nested" (check [] nested)
  assert "typed variable" (check [0] v)
  assert "lost integer assumption" (not (check [] v))
  assert "zero divisor" (not (check [] (G.LPPEDivide (c 7) (G.Int_of_integer 0))))
  assert "wrong quotient convention" (not (exact d (G.Fun G.IA4_Div [its 7,its (-3)])))
  assert "wrong remainder sign" (not (exact m (G.Fun G.IA4_Mod [neg (its 7),its 3])))
  assert "changed source operator" (not (G.lpp_check_expression_bridge [] (G.lpp_expression_term m) d (G.lpp_expression_its d)))
  let quoted = G.Fun (G.LPCUser (map (G.char_of_integer . toInteger . ord) "0:prolog_data_37")) []
  assert "quoted numeric atom" (not (G.lpp_check_expression_bridge [] quoted (c 7) (its 7)))
  assert "changed integer literal" (not (G.lpp_check_expression_bridge [] (G.lpp_expression_term (c 8)) (c 7) (its 7)))
  assert "changed target" (not (exact nested (its 0)))
  putStrLn "12 arithmetic bridge component checks passed (4 positive, 8 negative)"
