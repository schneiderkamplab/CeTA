theory LP_Prolog_Evaluated_Integer_Expressions
  imports LP_Prolog_Stable_Modulo LP_Prolog_Stable_Context LP_Prolog_Integer_Expression_Shapes
begin

text \<open>Reuse the integer expression language with leaves that are source
expressions rather than integer literals. Each leaf needs actual successful
integer evaluation. Neither groundness nor a successful comparison supplies
this premise; successful quotient/modulo observations can supply it through
their existing operand theorems. This does not change operational semantics.\<close>

theorem lpp_checked_evaluated_integer_expression:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_expression_check K expression"
    and leaves: "\<And>x. x\<in>set K \<Longrightarrow>
      lpp_stable_scalar_evaluation operation (eta x) (lpp_integer_value (rho x))"
  shows "lpp_stable_scalar_evaluation operation
    (lp_ieval (lpp_expression_term expression) eta)
    (lpp_integer_value (lpp_expression_value expression rho))"
  using checked
  by (induction expression)
    (auto simp: lpp_stable_integer_operations_def
      intro: leaves lpp_stable_integer_literal lpp_stable_scalar_evaluation.intros
        lpp_integer_scalar_observation dest: conjunct1 conjunct2
      simp: compatible[unfolded lpp_stable_integer_operations_def])

corollary lpp_checked_evaluated_integer_bound:
  assumes "lpp_stable_integer_operations operation"
    "lpp_expression_check K expression"
    "\<And>x. x\<in>set K \<Longrightarrow>
      lpp_stable_scalar_evaluation operation (eta x) (lpp_integer_value (rho x))"
  shows "lpp_stable_expression_bound operation
    (lp_ieval (lpp_expression_term expression) eta) = lpp_expression_value expression rho"
  by (rule lpp_stable_integer_bound[OF lpp_checked_evaluated_integer_expression[OF assms]])

fun lpp_evaluated_expression_term where
  "lpp_evaluated_expression_term (LPPEConstant n) = lpp_integer_term n"
| "lpp_evaluated_expression_term (LPPEVariable t) = t"
| "lpp_evaluated_expression_term (LPPEPositive a) = Fun (LPCUser ''1:prolog_data_2b'') [lpp_evaluated_expression_term a]"
| "lpp_evaluated_expression_term (LPPENegate a) = Fun (LPCUser ''1:prolog_data_2d'') [lpp_evaluated_expression_term a]"
| "lpp_evaluated_expression_term (LPPEAdd a b) = Fun (LPCUser ''2:prolog_data_2b'') [lpp_evaluated_expression_term a,lpp_evaluated_expression_term b]"
| "lpp_evaluated_expression_term (LPPESubtract a b) = Fun (LPCUser ''2:prolog_data_2d'') [lpp_evaluated_expression_term a,lpp_evaluated_expression_term b]"
| "lpp_evaluated_expression_term (LPPEMultiply a b) = Fun (LPCUser ''2:prolog_data_2a'') [lpp_evaluated_expression_term a,lpp_evaluated_expression_term b]"
| "lpp_evaluated_expression_term (LPPEDivide a d) = Fun (LPCUser ''2:prolog_data_646976'') [lpp_evaluated_expression_term a,lpp_integer_term d]"
| "lpp_evaluated_expression_term (LPPEModulo a d) = Fun (LPCUser ''2:prolog_data_6d6f64'') [lpp_evaluated_expression_term a,lpp_integer_term d]"

lemma lpp_evaluated_expression_term_eval:
  "lp_ieval (lpp_evaluated_expression_term e) eta =
    lp_ieval (lpp_expression_term e) (\<lambda>t. lp_ieval t eta)"
  by (induction e) auto

fun lpp_evaluated_integer_operands where
  "lpp_evaluated_integer_operands (Fun f [a,b]) =
    (if f=LPCUser ''2:prolog_data_6d6f64'' \<or> f=LPCUser ''2:prolog_data_2f2f''
      then [a,b,Fun f [a,b]] else [])"
| "lpp_evaluated_integer_operands t = []"

lemma lpp_evaluated_integer_operands_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval t eta) result"
    and member: "a\<in>set (lpp_evaluated_integer_operands t)"
  shows "\<exists>n. lpp_stable_scalar_evaluation operation (lp_ieval a eta) (lpp_integer_value n)"
proof -
  obtain f x y where source_shape: "t=Fun f [x,y]"
    and operator: "f=LPCUser ''2:prolog_data_6d6f64'' \<or> f=LPCUser ''2:prolog_data_2f2f''"
    and selected: "a=x \<or> a=y \<or> a=t"
    using member by (cases t rule: lpp_evaluated_integer_operands.cases) (auto split: if_splits)
  have operands: "\<exists>n d k.
    lpp_stable_scalar_evaluation operation (lp_ieval x eta) (lpp_integer_value n) \<and>
    lpp_stable_scalar_evaluation operation (lp_ieval y eta) (lpp_integer_value d) \<and>
    result=lpp_integer_value k"
  proof (cases "f=LPCUser ''2:prolog_data_6d6f64''")
    case True
    have ev: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [lp_ieval x eta,lp_ieval y eta]) result"
      using evaluated source_shape True by simp
    show ?thesis by (rule lpp_stable_modulo_operands[OF compatible ev]) blast
  next
    case False
    have ev: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval x eta,lp_ieval y eta]) result"
      using evaluated source_shape operator False by simp
    show ?thesis by (rule lpp_stable_quotient_operands[OF compatible ev]) blast
  qed
  show ?thesis using operands selected evaluated by blast
qed

fun lpp_observed_evaluated_integers where
  "lpp_observed_evaluated_integers (LPPOInteger t) = [t]"
| "lpp_observed_evaluated_integers (LPPOEvaluation e r) = lpp_evaluated_integer_operands e"
| "lpp_observed_evaluated_integers (LPPOComparison c a b) =
    lpp_evaluated_integer_operands a @ lpp_evaluated_integer_operands b"
| "lpp_observed_evaluated_integers (LPPOShape G shape t) =
    (if lpp_integer_expression_shape G shape then [t] else [])"
| "lpp_observed_evaluated_integers observation = []"

lemma lpp_stable_integer_shape_evaluation:
  assumes "lpp_stable_integer_operations operation" "lpp_integer_expression_shape G shape"
    "lp_return_shape_holds G shape t"
  shows "\<exists>n. lpp_stable_scalar_evaluation operation t (lpp_integer_value n)"
  using lpp_integer_expression_shape_sound[OF assms(2,3)]
    lpp_stable_evaluation_integer_exact[OF assms(1)] by blast

lemma lpp_observed_evaluated_integers_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and observed: "lpp_stable_observation_holds operation eta observation"
    and member: "t\<in>set (lpp_observed_evaluated_integers observation)"
  shows "\<exists>n. lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value n)"
  using observed member
  by (cases observation;
    auto simp: lpp_stable_compare_outcome_def lpp_stable_compare_values_def lpp_is_integer_def
      split: if_splits intro: lpp_evaluated_integer_operands_sound[OF compatible] lpp_stable_integer_shape_evaluation[OF compatible]; metis lpp_stable_integer_literal)

theorem lpp_observed_integer_expression_bound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and observations: "list_all (lpp_stable_observation_holds operation eta) ambient"
    and checked: "lpp_expression_check (concat (map lpp_observed_evaluated_integers ambient)) e"
  shows "lpp_stable_expression_bound operation (lp_ieval (lpp_evaluated_expression_term e) eta) =
    lpp_expression_value e (\<lambda>t. lpp_stable_expression_bound operation (lp_ieval t eta))"
proof -
  have leaf: "lpp_stable_scalar_evaluation operation (lp_ieval t eta)
      (lpp_integer_value (lpp_stable_expression_bound operation (lp_ieval t eta)))"
    if membership: "t\<in>set (concat (map lpp_observed_evaluated_integers ambient))" for t
  proof -
    obtain observation where member: "observation\<in>set ambient"
      and selected_term: "t\<in>set (lpp_observed_evaluated_integers observation)"
      using membership by (auto simp only: set_concat set_map)
    have observed: "lpp_stable_observation_holds operation eta observation"
      using observations member by (simp add: list_all_iff)
    obtain n where evaluated_leaf: "lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value n)"
      using lpp_observed_evaluated_integers_sound[OF compatible observed selected_term] by blast
    show ?thesis using evaluated_leaf lpp_stable_integer_bound[OF evaluated_leaf] by simp
  qed
  show ?thesis unfolding lpp_evaluated_expression_term_eval
    by (rule lpp_checked_evaluated_integer_bound[OF compatible checked leaf])
qed

definition lpp_evaluated_leaf where
  "lpp_evaluated_leaf bindings x = (case map_of bindings x of None \<Rightarrow> Var x | Some t \<Rightarrow> t)"

definition lpp_check_evaluated_expression where
  "lpp_check_evaluated_expression ambient bindings e =
    (distinct (map fst bindings) \<and> lpp_expression_check (map fst bindings) e \<and>
      list_all (\<lambda>(x,t). t\<in>set (concat (map lpp_observed_evaluated_integers ambient))) bindings)"

lemma lpp_expression_check_map:
  "lpp_expression_check K e \<Longrightarrow> lpp_expression_check (map f K) (map_lpp_integer_expression f e)"
  by (induction e) auto

lemma lpp_expression_check_mono:
  "lpp_expression_check K e \<Longrightarrow> (\<And>x. x\<in>set K \<Longrightarrow> x\<in>set L) \<Longrightarrow> lpp_expression_check L e"
  by (induction e) auto

lemma lpp_checked_evaluated_leaf:
  assumes "lpp_check_evaluated_expression ambient bindings e" "x\<in>set (map fst bindings)"
  shows "lpp_evaluated_leaf bindings x\<in>set (concat (map lpp_observed_evaluated_integers ambient))"
proof -
  obtain t where lookup: "map_of bindings x=Some t"
    using assms(2) by (cases "map_of bindings x") (auto simp: map_of_eq_None_iff)
  have member: "(x,t)\<in>set bindings" by (rule map_of_SomeD[OF lookup])
  show ?thesis using assms(1) member lookup
    by (auto simp: lpp_check_evaluated_expression_def lpp_evaluated_leaf_def list_all_iff)
qed

theorem lpp_checked_bound_expression:
  assumes compatible: "lpp_stable_integer_operations operation"
    and observations: "list_all (lpp_stable_observation_holds operation eta) ambient"
    and checked: "lpp_check_evaluated_expression ambient bindings e"
  shows "lpp_stable_expression_bound operation
      (lp_ieval (lpp_evaluated_expression_term (map_lpp_integer_expression (lpp_evaluated_leaf bindings) e)) eta) =
    lpp_expression_value e (\<lambda>x. lpp_stable_expression_bound operation (lp_ieval (lpp_evaluated_leaf bindings x) eta))"
proof -
  have local: "lpp_expression_check (map fst bindings) e"
    using checked by (simp add: lpp_check_evaluated_expression_def)
  have check: "lpp_expression_check (concat (map lpp_observed_evaluated_integers ambient))
      (map_lpp_integer_expression (lpp_evaluated_leaf bindings) e)"
    by (rule lpp_expression_check_mono[OF lpp_expression_check_map[OF local]])
      (use lpp_checked_evaluated_leaf[OF checked] in auto)
  show ?thesis using lpp_observed_integer_expression_bound[OF compatible observations check]
    by (simp add: lpp_expression_rename_value o_def)
qed

lemma lpp_stable_floor_order:
  assumes order: "c=LPPIntLess \<or> c=LPPIntLessEqual"
    and observed: "lpp_stable_compare_outcome operation c a b (LPPBuiltinSuccess LPIVar)"
  shows "lpp_stable_expression_bound operation a \<le> lpp_stable_expression_bound operation b"
proof -
  obtain v w n d m e where left: "lpp_stable_scalar_evaluation operation a v"
    and right: "lpp_stable_scalar_evaluation operation b w"
    and lv: "lpp_scalar_fraction v n d" and rv: "lpp_scalar_fraction w m e"
    and compared: "lpp_integer_compare c (n*e) (m*d)"
    using observed by (auto simp: lpp_stable_compare_outcome_def lpp_stable_compare_values_def split: if_splits)
  have dp: "0<d" and ep: "0<e"
    using lpp_scalar_fraction_denominator[OF lv] lpp_scalar_fraction_denominator[OF rv] by auto
  have cross: "n*e\<le>m*d" using compared order by auto
  have real_cross: "(of_int n :: real) * of_int e \<le> of_int m * of_int d"
    using of_int_le_iff[of "n*e" "m*d", where 'a=real] cross
    by (simp only: of_int_mult)
  have rational: "(of_int n / of_int d :: real) \<le> of_int m / of_int e"
    using dp ep real_cross by (simp add: field_simps)
  have floors: "n div d \<le> m div e"
    using floor_mono[OF rational] by (simp add: floor_divide_of_int_eq)
  show ?thesis using floors
    by (simp add: lpp_stable_expression_bound_exact[OF left] lpp_stable_expression_bound_exact[OF right]
      lpp_scalar_floor_exact[OF lv] lpp_scalar_floor_exact[OF rv])
qed

ML \<open>
val checked = [@{thm lpp_checked_evaluated_integer_expression},
  @{thm lpp_checked_evaluated_integer_bound}, @{thm lpp_evaluated_integer_operands_sound},
  @{thm lpp_observed_evaluated_integers_sound}, @{thm lpp_observed_integer_expression_bound},
  @{thm lpp_checked_bound_expression}, @{thm lpp_stable_floor_order}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted evaluated integer expression dependency" else ();
\<close>
end
