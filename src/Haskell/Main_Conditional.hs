-- Native conditional descent certificates. All original rules and ordered
-- conditions are retained. The generated checker validates every step.
module Main (main) where
import qualified Conditional_Checker as C
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Read (readMaybe)
import Data.Char (ord)

data Term = V String | F String [Term] deriving Read
type Rule = ((Term,Term),[(Term,Term)])
type Subst = [(String,Term)]
data Rewrite = RewriteStep Integer [Integer] Subst Term Term [[Rewrite]] deriving Read
data Step = Rewrite Rewrite | Call Integer Subst Integer [[Rewrite]] Term Term
          | Argument Term Integer deriving Read
data Certificate = ConditionalCycle [Rule] Term [Step]
                 | ConditionalLoop [Rule] Term [Step] Subst deriving Read

-- Injective, name-independent encoding, including the empty identifier.
name :: String -> Integer
name = foldl (\n c -> n * 1114113 + toInteger (ord c) + 1) 1
term (V v) = C.Var [name v]
term (F f ts) = C.Fun (name f) (map term ts)
pair (s,t) = (term s,term t)
rule (lr,cs) = (pair lr,map pair cs)
substitution xs = C.conditional_substitution (map (\(v,t)->([name v],term t)) xs)

rewrite rs (RewriteStep k pos sub s t ps)
  | k < 0 || k >= toInteger (length rs) || any (<0) pos = Nothing
  | otherwise = do
      children <- mapM (mapM (rewrite rs)) ps
      return (C.Cstep_step (rule (rs !! fromInteger k)) (map C.nat_of_integer pos)
        (substitution sub) (term s) (term t) children)
step rs (Rewrite p) = fmap C.Conditional_rewrite (rewrite rs p)
step rs (Call k sub i ps s t)
  | k < 0 || i < 0 = Nothing
  | otherwise = do
      children <- mapM (mapM (rewrite rs)) ps
      return (C.Conditional_call (C.nat_of_integer k) (substitution sub)
        (C.nat_of_integer i) children (term s) (term t))
step _ (Argument (F f ts) i)
  | i >= 0 = Just (C.Conditional_argument (name f) (map term ts) (C.nat_of_integer i))
step _ _ = Nothing

check (ConditionalCycle rs s ps) = case mapM (step rs) ps of
  Just steps -> C.conditional_check (map rule rs) (term s) steps ||
    C.conditional_check_rewrite_loop (map rule rs) (term s) steps []
  Nothing -> False
check (ConditionalLoop rs s ps sub) = case mapM (step rs) ps of
  Just steps -> let subst = map (\(v,t)->([name v],term t)) sub in
    C.conditional_check_loop (map rule rs) (term s) steps subst ||
    C.conditional_check_rewrite_loop (map rule rs) (term s) steps subst
  Nothing -> False
checkOrdinary (ConditionalCycle rs s ps) = case mapM (step rs) ps of
  Just steps -> C.conditional_check_rewrite_loop (map rule rs) (term s) steps []
  Nothing -> False
checkOrdinary (ConditionalLoop rs s ps sub) = case mapM (step rs) ps of
  Just steps -> C.conditional_check_rewrite_loop (map rule rs) (term s) steps
    (map (\(v,t)->([name v],term t)) sub)
  Nothing -> False

main = do
  args <- getArgs
  case args of
    ["--ordinary", path] -> do
      text <- readFile path
      case readMaybe text of
        Just cert | checkOrdinary cert -> putStrLn "CERTIFIED"
        _ -> putStrLn "REJECTED" >> exitFailure
    [path] -> do
      text <- readFile path
      case readMaybe text of
        Just cert | check cert -> putStrLn "CERTIFIED"
        _ -> putStrLn "REJECTED" >> exitFailure
    _ -> putStrLn "usage: ceta-conditional CERTIFICATE" >> exitFailure
