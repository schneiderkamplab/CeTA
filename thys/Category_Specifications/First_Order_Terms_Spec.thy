theory First_Order_Terms_Spec
  imports Main
begin

text \<open>Finite first-order terms consist of variables and function applications.
These raw terms carry no signature restriction; ranked rewriting adds it separately.\<close>
datatype ('f, 'v) fo_term = SVar 'v | SFun 'f "('f, 'v) fo_term list"

text \<open>Substitution replaces variables simultaneously by finite terms,
which may themselves contain variables.\<close>
fun fo_subst :: "('v \<Rightarrow> ('f, 'v) fo_term) \<Rightarrow> ('f, 'v) fo_term \<Rightarrow> ('f, 'v) fo_term" where
  "fo_subst s (SVar x) = s x"
| "fo_subst s (SFun f ts) = SFun f (map (fo_subst s) ts)"

text \<open>A context has exactly one hole. Its lists contain the left and right
siblings; plugging fills the hole at any depth.\<close>
datatype ('f, 'v) fo_context = SHole
  | SMore 'f "('f, 'v) fo_term list" "('f, 'v) fo_context" "('f, 'v) fo_term list"
fun fo_plug where
  "fo_plug SHole t = t"
| "fo_plug (SMore f ls C rs) t = SFun f (ls @ fo_plug C t # rs)"

end
