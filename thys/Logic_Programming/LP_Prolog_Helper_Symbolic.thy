theory LP_Prolog_Helper_Symbolic
  imports LP_Prolog_Helper_Call_Row LP_Prolog_Integer_Call_Formula
begin

text \<open>Numeric expressions for helper calls reuse the established expression
substitution and guard machinery. Their equalities below are exact; source
argument and freshness premises remain in the separate call-row checker.\<close>

definition lpp_bind_expressions where
  "lpp_bind_expressions xs expressions x =
    (case map_of (zip xs expressions) x of None \<Rightarrow> LPPEConstant 0 | Some e \<Rightarrow> e)"

lemma lpp_bind_expressions_value:
  "lpp_expression_value (lpp_bind_expressions xs expressions x) rho =
    lpp_recurrence_arguments xs (map (\<lambda>e. lpp_expression_value e rho) expressions) x"
proof (induct xs arbitrary: expressions)
  case Nil show ?case by (simp add: lpp_bind_expressions_def lpp_recurrence_arguments_def)
next
  case (Cons y ys)
  show ?case by (cases expressions)
    (auto simp: lpp_bind_expressions_def lpp_recurrence_arguments_def
      Cons.hyps[unfolded lpp_bind_expressions_def lpp_recurrence_arguments_def])
qed

definition lpp_helper_symbolic_arguments where
  "lpp_helper_symbolic_arguments s env = lpp_bind_expressions (lpphr_head (lpphs_recipe s))
    (map (lpp_recurrence_substitute env) (lpphs_numeric s))"
definition lpp_helper_symbolic_value where
  "lpp_helper_symbolic_value s env = lpp_recurrence_substitute
    (lpp_recurrence_symbolic_values (lpphr_prefix (lpphs_recipe s)) (lpp_helper_symbolic_arguments s env))
    (lpphr_expression (lpphs_recipe s))"
definition lpp_helper_symbolic_guards where
  "lpp_helper_symbolic_guards s env = lpp_recurrence_symbolic_guards
    (lpphr_prefix (lpphs_recipe s)) (lpp_helper_symbolic_arguments s env)"

lemma lpp_helper_symbolic_arguments_exact:
  "(\<lambda>x. lpp_expression_value (lpp_helper_symbolic_arguments s env x) rho) =
    lpp_helper_site_environment s (\<lambda>x. lpp_expression_value (env x) rho)"
  by (rule ext) (simp add: lpp_helper_symbolic_arguments_def lpp_bind_expressions_value
    lpp_helper_site_environment_def lpp_helper_site_arguments_def map_map lpp_recurrence_substitute_value o_def)

lemma lpp_helper_symbolic_value_exact:
  "lpp_expression_value (lpp_helper_symbolic_value s env) rho =
    lpp_helper_site_value s (\<lambda>x. lpp_expression_value (env x) rho)"
  by (simp add: lpp_helper_symbolic_value_def lpp_recurrence_substitute_value
    lpp_recurrence_symbolic_values_exact lpp_helper_symbolic_arguments_exact lpp_helper_site_value_def)

lemma lpp_helper_symbolic_guards_exact:
  "list_all (lpp_numeric_condition_holds rho) (lpp_helper_symbolic_guards s env) =
    lpp_helper_site_guards s (\<lambda>x. lpp_expression_value (env x) rho)"
  by (simp add: lpp_helper_symbolic_guards_def lpp_recurrence_symbolic_guards_exact
    lpp_helper_symbolic_arguments_exact lpp_helper_site_guards_def)

fun lpp_helper_operation_symbolic_values where
  "lpp_helper_operation_symbolic_values (LPPHPrimitive op) env = lpp_recurrence_symbolic_values [op] env"
| "lpp_helper_operation_symbolic_values (LPPHCall s) env = env(lpphs_output s:=lpp_helper_symbolic_value s env)"
fun lpp_helper_operation_symbolic_guards where
  "lpp_helper_operation_symbolic_guards (LPPHPrimitive op) env = lpp_recurrence_symbolic_guards [op] env"
| "lpp_helper_operation_symbolic_guards (LPPHCall s) env = lpp_helper_symbolic_guards s env"

lemma lpp_helper_operation_symbolic_values_exact:
  "(\<lambda>x. lpp_expression_value (lpp_helper_operation_symbolic_values op env x) rho) =
    lpp_helper_operation_values op (\<lambda>x. lpp_expression_value (env x) rho)"
proof (cases op)
  case (LPPHPrimitive primitive)
  show ?thesis using lpp_recurrence_symbolic_values_exact[of "[primitive]" env rho]
    by (simp only: LPPHPrimitive lpp_helper_operation_symbolic_values.simps lpp_helper_operation_values.simps)
next
  case (LPPHCall s)
  show ?thesis by (rule ext) (simp add: LPPHCall lpp_helper_symbolic_value_exact)
qed

lemma lpp_helper_operation_symbolic_guards_exact:
  "list_all (lpp_numeric_condition_holds rho) (lpp_helper_operation_symbolic_guards op env) =
    lpp_helper_operation_guards op (\<lambda>x. lpp_expression_value (env x) rho)"
  by (cases op) (simp_all add: lpp_recurrence_symbolic_guards_exact lpp_helper_symbolic_guards_exact)

fun lpp_helper_prefix_symbolic_values where
  "lpp_helper_prefix_symbolic_values [] env = env"
| "lpp_helper_prefix_symbolic_values (op#ops) env =
    lpp_helper_prefix_symbolic_values ops (lpp_helper_operation_symbolic_values op env)"
fun lpp_helper_prefix_symbolic_guards where
  "lpp_helper_prefix_symbolic_guards [] env = []"
| "lpp_helper_prefix_symbolic_guards (op#ops) env =
    lpp_helper_operation_symbolic_guards op env @
      lpp_helper_prefix_symbolic_guards ops (lpp_helper_operation_symbolic_values op env)"

lemma lpp_helper_prefix_symbolic_values_exact:
  "(\<lambda>x. lpp_expression_value (lpp_helper_prefix_symbolic_values ops env x) rho) =
    lpp_helper_prefix_values ops (\<lambda>x. lpp_expression_value (env x) rho)"
  by (induct ops arbitrary: env)
    (simp_all only: lpp_helper_prefix_symbolic_values.simps lpp_helper_prefix_values.simps
      lpp_helper_operation_symbolic_values_exact)

lemma lpp_helper_prefix_symbolic_guards_exact:
  "list_all (lpp_numeric_condition_holds rho) (lpp_helper_prefix_symbolic_guards ops env) =
    lpp_helper_prefix_guards ops (\<lambda>x. lpp_expression_value (env x) rho)"
  by (induct ops arbitrary: env)
    (simp_all only: lpp_helper_prefix_symbolic_guards.simps lpp_helper_prefix_guards.simps
      list_all_Nil_iff list_all_append lpp_helper_operation_symbolic_guards_exact
      lpp_helper_operation_symbolic_values_exact)

ML \<open>
val checked = [@{thm lpp_helper_prefix_symbolic_values_exact}, @{thm lpp_helper_prefix_symbolic_guards_exact}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper symbolic arithmetic" else ();
\<close>
end
