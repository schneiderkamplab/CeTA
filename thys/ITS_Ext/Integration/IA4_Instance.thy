theory IA4_Instance
  imports ITS_Arithmetic.IA4_Definability
begin


global_interpretation IA4Check: logic_checker
  where type_fixer = "TYPE(_)"
    and I = IA4.I and type_of_fun = IA4.type_of_fun
    and Values_of_type = IA.Values_of_type and Bool_types = "{IA.BoolT}"
    and to_bool = IA.to_bool
    and logic_checker = ia4_check_clause
    and showsl_atom = showsl
    and normalize_lit = "\<lambda>b e. if b then Atom e else NegAtom e"
    and normalized_lit = "\<lambda>_ _. True"
  by (unfold_locales; auto simp: pre_logic_checker.normalized_formula.simps intro: ia4_check_clause_sound)


abbreviation ia4_le where "ia4_le s t \<equiv> Atom (Fun (IA4_Base IA.LeF) [s,t])"
abbreviation ia4_less where "ia4_less s t \<equiv> Atom (Fun (IA4_Base IA.LessF) [s,t])"

lemma ia4_le_meaning:
  assumes "IA4.assignment alpha" "IA4.has_type s IA.IntT" "IA4.has_type t IA.IntT"
  shows "IA4.satisfies alpha (ia4_le s t) = (IA4.eval s alpha \<le> IA4.eval t alpha)"
  using IA4.eval_types[OF assms(1-2)] IA4.eval_types[OF assms(1,3)]
  by (cases "IA4.eval s alpha"; cases "IA4.eval t alpha"; auto)
lemma ia4_less_meaning:
  assumes "IA4.assignment alpha" "IA4.has_type s IA.IntT" "IA4.has_type t IA.IntT"
  shows "IA4.satisfies alpha (ia4_less s t) = (IA4.eval s alpha < IA4.eval t alpha)"
  using IA4.eval_types[OF assms(1-2)] IA4.eval_types[OF assms(1,3)]
  by (cases "IA4.eval s alpha"; cases "IA4.eval t alpha"; auto)

global_interpretation IA4Termination: termination_checker
  where type_fixer = "TYPE(_)"
    and I = IA4.I and type_of_fun = IA4.type_of_fun
    and Values_of_type = IA.Values_of_type and Bool_types = "{IA.BoolT}"
    and to_bool = IA.to_bool
    and sa = showsl and sa2 = showsl
    and tc = ia4_check_clause and tc2 = ia4_check_clause
    and ne = "\<lambda>b e. if b then Atom e else NegAtom e"
    and ne2 = "\<lambda>b e. if b then Atom e else NegAtom e"
    and ned = "\<lambda>_ _. True" and ned2 = "\<lambda>_ _. True"
    and dom_type = IA.IntT
    and less_eq = "(\<le>) :: IA.val \<Rightarrow> _ \<Rightarrow> _" and less = "(<)"
    and less_eq_formula = ia4_le and less_formula = ia4_less
    and definability_checker = ia4_def_checker
    and is_constant = "\<lambda>e. vars_term e = {}"
  by (unfold_locales;
    (fact ia4_le_meaning ia4_less_meaning ia4_def_checker_sound constant_eval | simp add: All_less_Suc))

definition ia4_check_termination where "ia4_check_termination = IA4Termination.check"
lemma ia4_check_termination_sound:
  "isOK (ia4_check_termination P proof) \<Longrightarrow> IA4Termination.lts_termination (lts_of P)"
  unfolding ia4_check_termination_def by (rule IA4Termination.sound)
declare ia4_check_termination_def[code]
end
