theory Higher_Order_Algebraic_Embedding
  imports Higher_Order_Finite_Branching
begin

text \<open>The first-order fragment is represented explicitly. Its
substitutions may contain arbitrary higher-order source terms; no erasure of
those terms, their types, or beta reduction is justified by this embedding.\<close>

datatype ho_fo_tree = HFOVar nat | HFOFun nat "ho_fo_tree list"

fun ho_fo_variables where
  "ho_fo_variables (HFOVar n) = {n}"
| "ho_fo_variables (HFOFun c ts) = \<Union>(ho_fo_variables ` set ts)"

fun ho_fo_wellformed where
  "ho_fo_wellformed F arity (HFOVar n) = True"
| "ho_fo_wellformed F arity (HFOFun c ts) =
    (c\<in>F \<and> length ts=arity c \<and> list_all (ho_fo_wellformed F arity) ts)"

fun ho_fo_substitution where
  "ho_fo_substitution s (HFOVar n) = s n"
| "ho_fo_substitution s (HFOFun c ts) = HFOFun c (map (ho_fo_substitution s) ts)"

fun ho_fo_instance where
  "ho_fo_instance s (HFOVar n) = s n"
| "ho_fo_instance s (HFOFun c ts) = ho_apply_terms (HConst c) (map (ho_fo_instance s) ts)"

fun ho_fo_pattern where
  "ho_fo_pattern (HFOVar n) = PMeta n []"
| "ho_fo_pattern (HFOFun c ts) = foldl PApp (PConst c) (map ho_fo_pattern ts)"

lemma ho_subst_fo_instance:
  "ho_subst s d (ho_fo_instance q t) = ho_fo_instance (\<lambda>n. ho_subst s d (q n)) t"
  by (induction t) (auto simp: ho_subst_apply_terms map_map cong: map_cong)

lemma ho_erase_fold_application:
  "ho_erase_pattern (foldl PApp p ps) = ho_apply_terms (ho_erase_pattern p) (map ho_erase_pattern ps)"
  by (induction ps arbitrary: p) auto

lemma ho_zero_fold_application:
  "ho_zero_arity_pattern (foldl PApp p ps) \<longleftrightarrow>
    ho_zero_arity_pattern p \<and> list_all ho_zero_arity_pattern ps"
  by (induction ps arbitrary: p) auto

lemma ho_fo_pattern_zero:
  "ho_zero_arity_pattern (ho_fo_pattern t)"
  by (induction t) (auto simp: ho_zero_fold_application list_all_iff)

lemma ho_fo_pattern_erase:
  "ho_erase_pattern (ho_fo_pattern t) = ho_fo_instance HFree t"
  by (induction t) (auto simp: ho_erase_fold_application map_map cong: map_cong)

lemma ho_fo_pattern_instantiate:
  "ho_instantiate s 0 (ho_fo_pattern t) = Some (ho_fo_instance s t)"
  by (simp add: ho_zero_arity_instantiate[OF ho_fo_pattern_zero]
      ho_fo_pattern_erase ho_subst_fo_instance ho_lift_0)

theorem ho_algebraic_root_instance:
  assumes member: "(G,ho_fo_pattern l,ho_fo_pattern r)\<in>set R"
    and typed: "ho_rule_welltyped S (G,ho_fo_pattern l,ho_fo_pattern r)"
    and subst: "ho_typed_subst S V B G s"
  shows "ho_root_step S V R B (ho_fo_instance s l) (ho_fo_instance s r)"
  unfolding ho_root_step_def
  using member typed subst ho_fo_pattern_instantiate by blast

corollary ho_algebraic_source_step:
  "(G,ho_fo_pattern l,ho_fo_pattern r)\<in>set R \<Longrightarrow>
    ho_rule_welltyped S (G,ho_fo_pattern l,ho_fo_pattern r) \<Longrightarrow>
    ho_typed_subst S V B G s \<Longrightarrow>
    ho_step S V R B (ho_fo_instance s l) (ho_fo_instance s r)"
  by (rule ho_step.rule) (assumption+, simp_all add: ho_fo_pattern_instantiate)

end
