theory IA4_Checker
  imports IA4_Normalization
begin

definition lower_formula where "lower_formula f = map_formula lower_exp f"
fun formula_constraints where
  "formula_constraints (Atom e) = constraints e"
| "formula_constraints (NegAtom e) = constraints e"
| "formula_constraints (Conjunction fs) = concat (map formula_constraints fs)"
| "formula_constraints (Disjunction fs) = concat (map formula_constraints fs)"
fun supported_formula where
  "supported_formula (Atom e) = supported_exp e"
| "supported_formula (NegAtom e) = supported_exp e"
| "supported_formula (Conjunction fs) = list_all supported_formula fs"
| "supported_formula (Disjunction fs) = list_all supported_formula fs"

lemma lower_formula_type:
  "IA4.formula f \<Longrightarrow> IA.formula (lower_formula f)"
  unfolding lower_formula_def
  by (induct f, auto simp: IA4.is_bool_def IA.is_bool_def intro: lower_exp_type)

lemma lower_formula_satisfied:
  "IA4.formula f \<Longrightarrow>
   IA.satisfies (lifted_valuation alpha) (lower_formula f) = IA4.satisfies alpha f"
  unfolding lower_formula_def
  by (induct f, auto simp: IA4.is_bool_def IA.is_bool_def lower_exp_eval)

lemma formula_constraints_type:
  "IA4.formula f \<Longrightarrow> IA.formula (Conjunction (formula_constraints f))"
  by (induct f, auto simp: IA4.is_bool_def intro: constraints_type)

lemma formula_constraints_satisfied:
  "IA4.assignment alpha \<Longrightarrow> IA4.formula f \<Longrightarrow> supported_formula f \<Longrightarrow>
   IA.satisfies (lifted_valuation alpha) (Conjunction (formula_constraints f))"
  by (induct f, auto simp: IA4.is_bool_def list_all_iff dest: constraints_satisfied)

definition elimination_formula where
  "elimination_formula f = Disjunction [\<not>\<^sub>f Conjunction (formula_constraints f),lower_formula f]"

lemma elimination_formula_type:
  "IA4.formula f \<Longrightarrow> IA.formula (elimination_formula f)"
  unfolding elimination_formula_def using lower_formula_type formula_constraints_type by auto

lemma elimination_sound:
  fixes f :: "'v ia4_exp formula"
  assumes "IA4.formula f" "supported_formula f" "IA.valid (elimination_formula f)"
  shows "IA4.valid f"
proof (rule IA4.validI)
  fix alpha :: "'v \<times> IA.ty \<Rightarrow> IA.val" assume a: "IA4.assignment alpha"
  from IA.validD[OF assms(3) lifted_assignment[OF a]]
    formula_constraints_satisfied[OF a assms(1-2)] lower_formula_satisfied[OF assms(1), of alpha]
  show "IA4.satisfies alpha f" by (simp add: elimination_formula_def)
qed

definition ia4_check_clause where
  "ia4_check_clause h f = do {
    check (supported_formula f) (showsl_lit (STR ''div/mod requires a nonzero constant divisor''));
    IA.check_valid_formula h (elimination_formula f)
  }"

lemma ia4_check_clause_sound:
  "isOK (ia4_check_clause h f) \<Longrightarrow> IA4.formula f \<Longrightarrow> IA4.valid f"
  unfolding ia4_check_clause_def
  by (auto intro: elimination_sound IA.check_valid_formula elimination_formula_type)

end
