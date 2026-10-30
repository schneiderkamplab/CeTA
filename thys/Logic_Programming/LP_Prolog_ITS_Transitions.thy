theory LP_Prolog_ITS_Transitions
  imports LP_Prolog_Numeric_Guards LTS.LTS
begin

text \<open>The row bridge targets CeTA's actual labelled transition semantics.
Integer assignments also define Boolean-typed variables correctly; a function
returning an integer at every type is not a well-typed ITS assignment.\<close>

global_interpretation LPPIntegerLTS: lts
  where type_fixer="TYPE(_)" and I=IA4.I and type_of_fun=IA4.type_of_fun
    and Values_of_type=IA.Values_of_type and Bool_types="{IA.BoolT}" and to_bool=IA.to_bool .

fun lpp_integer_assignment where
  "lpp_integer_assignment rho (x,IA.IntT) = IA.Int (rho x)"
| "lpp_integer_assignment rho (x,IA.BoolT) = IA.Bool False"

lemma lpp_integer_assignment_typed:
  "IA4.assignment (lpp_integer_assignment rho)"
  by (rule IA4.assignmentI) (rename_tac x ty, case_tac ty, auto)

lemma lpp_expression_typed_assignment:
  "IA4.eval (lpp_expression_its e) (lpp_integer_assignment rho) =
    IA.Int (lpp_expression_value e rho)"
  by (induct e)
    (simp_all add: algebra.eval.simps euclid_quot_def euclid_rem_def div_minus_right mod_minus_right Let_def)

lemma lpp_comparison_typed_assignment:
  "IA4.satisfies (lpp_integer_assignment rho)
      (lpp_comparison_its comparison (lpp_expression_its a) (lpp_expression_its b)) =
    lpp_integer_compare comparison (lpp_expression_value a rho) (lpp_expression_value b rho)"
  by (cases comparison) (auto simp: lpp_expression_typed_assignment algebra.eval.simps)

fun lpp_trans_integer where
  "lpp_trans_integer before after middle (Pre x) = before x"
| "lpp_trans_integer before after middle (Post x) = after x"
| "lpp_trans_integer before after middle (Intermediate x) = middle x"

lemma lpp_pre_post_integer_assignment:
  fixes before after middle :: "'a \<Rightarrow> int"
  shows "LPPIntegerLTS.pre_post_inter (lpp_integer_assignment before)
      (lpp_integer_assignment after) (lpp_integer_assignment middle) =
    lpp_integer_assignment (lpp_trans_integer before after middle)"
proof (rule ext)
  fix x :: "'a trans_var * IA.ty"
  obtain v ty where x: "x=(v,ty)" by (cases x) auto
  show "LPPIntegerLTS.pre_post_inter (lpp_integer_assignment before)
      (lpp_integer_assignment after) (lpp_integer_assignment middle) x =
    lpp_integer_assignment (lpp_trans_integer before after middle) x"
    by (cases v; cases ty) (auto simp: x)
qed

type_synonym 'v lpp_numeric_condition =
  "lpp_integer_comparison \<times> 'v lpp_integer_expression \<times> 'v lpp_integer_expression"

fun lpp_numeric_condition_holds where
  "lpp_numeric_condition_holds rho (comparison,a,b) =
    lpp_integer_compare comparison (lpp_expression_value a rho) (lpp_expression_value b rho)"
fun lpp_numeric_condition_formula where
  "lpp_numeric_condition_formula (comparison,a,b) =
    lpp_comparison_its comparison (lpp_expression_its a) (lpp_expression_its b)"

definition lpp_numeric_row where
  "lpp_numeric_row from to numeric_tests = Transition from to
    (Conjunction (map lpp_numeric_condition_formula numeric_tests))"

lemma lpp_numeric_row_typed:
  "LPPIntegerLTS.transition_rule (lpp_numeric_row from to numeric_tests)"
  by (auto simp: lpp_numeric_row_def lpp_comparison_its_type list_all_iff split: prod.splits)

theorem lpp_numeric_row_step:
  assumes member: "lpp_numeric_row from to numeric_tests\<in>transition_rules system"
    and before: "IA4.satisfies (lpp_integer_assignment pre) (assertion system from)"
    and after: "IA4.satisfies (lpp_integer_assignment post) (assertion system to)"
    and numeric_tests: "list_all (lpp_numeric_condition_holds (lpp_trans_integer pre post middle)) numeric_tests"
  shows "(State (lpp_integer_assignment pre) from,State (lpp_integer_assignment post) to)
    \<in>LPPIntegerLTS.transition system"
proof (rule LPPIntegerLTS.mem_transitionI[OF member])
  show "(State (lpp_integer_assignment pre) from,State (lpp_integer_assignment post) to)
    \<in>LPPIntegerLTS.transition_step_lts system (lpp_numeric_row from to numeric_tests)"
    unfolding lpp_numeric_row_def
    by (rule LPPIntegerLTS.mem_transition_step_TransitionI[where \<gamma>="lpp_integer_assignment middle"])
      (use before after numeric_tests in \<open>auto simp: lpp_integer_assignment_typed
        lpp_pre_post_integer_assignment list_all_iff lpp_comparison_typed_assignment split: prod.splits\<close>)
qed

text \<open>CPF auxiliaries may occupy fresh post-state coordinates. Their
values need not be a function of the projected Prolog call. Relational
simulation permits choosing those coordinates for each source step while
preserving the complete target valuation along the simulated run.\<close>

lemma lpp_typed_relational_simulation_SN:
  assumes typed: "\<And>a b. (a,b)\<in>R \<Longrightarrow> T b"
    and start: "\<And>a. T a \<Longrightarrow> \<exists>s. rep a s \<and> SN_on S {s}"
    and simulate: "\<And>a b s. (a,b)\<in>R \<Longrightarrow> T a \<Longrightarrow> rep a s \<Longrightarrow>
      \<exists>t. (s,t)\<in>S \<and> rep b t"
  shows "SN R"
proof -
  have represented: "\<forall>a. T a \<longrightarrow> rep a s \<longrightarrow> SN_on R {a}"
    if sn: "SN_on S {s}" for s
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix s a
    assume ih: "\<And>t. (s,t)\<in>S \<Longrightarrow> \<forall>a. T a \<longrightarrow> rep a t \<longrightarrow> SN_on R {a}"
      and ta: "T a" and ra: "rep a s"
    show "SN_on R {a}"
    proof (rule step_reflects_SN_on)
      fix b assume edge: "(a,b)\<in>R"
      obtain t where target: "(s,t)\<in>S" and rb: "rep b t"
        using simulate[OF edge ta ra] by blast
      show "SN_on R {b}" using ih[OF target] typed[OF edge] rb by blast
    qed
  qed
  have typed_sn: "SN_on R {a}" if "T a" for a
    using start[OF that] represented that by blast
  have "SN_on R {a}" for a
    by (rule step_reflects_SN_on) (use typed typed_sn in blast)
  then show ?thesis by (simp add: SN_defs)
qed

ML \<open>
val checked = [@{thm lpp_integer_assignment_typed}, @{thm lpp_numeric_row_typed},
  @{thm lpp_numeric_row_step}, @{thm lpp_typed_relational_simulation_SN}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted numeric transition dependency" else ();
\<close>
end
