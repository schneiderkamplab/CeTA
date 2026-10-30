theory LP_Prolog_Numeric_Path
  imports LP_Prolog_Numeric_Row_Check
begin

text \<open>Whole numeric rows include both endpoint tuples and every arithmetic
observation. Checking only the guards would permit replacing the recursive
call by an unrelated terminating update. Endpoint terms must already denote
integers; a structural arithmetic expression is not evaluated implicitly.\<close>

fun lpp_integer_endpoint where
  "lpp_integer_endpoint (LPPEConstant n) = True"
| "lpp_integer_endpoint (LPPEVariable x) = True"
| "lpp_integer_endpoint _ = False"

type_synonym 'v lpp_numeric_endpoint =
  "string * (string lp_cut_symbol,'v) term * 'v lpp_integer_expression"

fun lpp_check_numeric_endpoint where
  "lpp_check_numeric_endpoint K (coordinate,t,e) =
    (t=lpp_expression_term e \<and> lpp_integer_endpoint e \<and> lpp_expression_check K e)"

lemma lpp_checked_numeric_endpoint:
  assumes checked: "lpp_check_numeric_endpoint K (coordinate,t,e)"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lp_ieval t eta=lpp_integer_value (lpp_expression_value e rho)"
  using checked typed by (cases e) auto

fun lpp_numeric_endpoint_formula where
  "lpp_numeric_endpoint_formula tag rename (coordinate,t,e) =
    lpp_comparison_its LPPIntEqual (Var (tag coordinate,IA.IntT))
      (lpp_expression_its (map_lpp_integer_expression rename e))"

fun lpp_numeric_input_formula where
  "lpp_numeric_input_formula rename (coordinate,t,e) =
    (if Var (Pre coordinate,IA.IntT)=lpp_expression_its (map_lpp_integer_expression rename e)
     then [] else [lpp_numeric_endpoint_formula Pre rename (coordinate,t,e)])"

definition lpp_numeric_path_formula where
  "lpp_numeric_path_formula inputs outputs numeric_tests bindings =
    (let rename=lpp_numeric_rename bindings in Conjunction
      (concat (map (lpp_numeric_input_formula rename) inputs) @
       map (lpp_numeric_condition_formula o lpp_rename_numeric_condition rename) numeric_tests @
       map (lpp_numeric_endpoint_formula Post rename) outputs))"

definition lpp_check_numeric_path where
  "lpp_check_numeric_path K inputs outputs observations numeric_tests bindings formula =
    (list_all (lpp_check_numeric_endpoint K) inputs \<and>
     list_all (lpp_check_numeric_endpoint K) outputs \<and>
     distinct (map fst inputs) \<and> distinct (map fst outputs) \<and>
     distinct (map fst bindings) \<and> list_all (\<lambda>x. map_of bindings x\<noteq>None) K \<and>
     list_all2 (lpp_check_numeric_observation K) observations numeric_tests \<and>
     formula=lpp_numeric_path_formula inputs outputs numeric_tests bindings)"

lemma lpp_numeric_endpoint_formula_sound:
  assumes checked: "lpp_check_numeric_endpoint K endpoint"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho (rename x))"
    and represented: "lp_ieval (fst (snd endpoint)) eta=lpp_integer_value (rho (tag (fst endpoint)))"
  shows "IA4.satisfies (lpp_integer_assignment rho) (lpp_numeric_endpoint_formula tag rename endpoint)"
proof -
  obtain coordinate t e where endpoint: "endpoint=(coordinate,t,e)" by (cases endpoint) auto
  have evaluated: "lp_ieval t eta=lpp_integer_value (lpp_expression_value e (rho o rename))"
    by (rule lpp_checked_numeric_endpoint[OF checked[unfolded endpoint]]) (use typed in auto)
  have same: "rho (tag coordinate)=lpp_expression_value e (rho o rename)"
    using evaluated represented by (simp add: endpoint lpp_integer_value_def)
  show ?thesis by (simp add: endpoint lpp_expression_typed_assignment
    lpp_expression_rename_value same algebra.eval.simps)
qed

theorem lpp_check_numeric_path_sound:
  assumes checked: "lpp_check_numeric_path K inputs outputs observations numeric_tests bindings formula"
    and observed: "list_all (lpp_numeric_observation_holds eta) observations"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho (lpp_numeric_rename bindings x))"
    and inputs: "\<And>name t e. (name,t,e)\<in>set inputs \<Longrightarrow> lp_ieval t eta=lpp_integer_value (rho (Pre name))"
    and outputs: "\<And>name t e. (name,t,e)\<in>set outputs \<Longrightarrow> lp_ieval t eta=lpp_integer_value (rho (Post name))"
  shows "IA4.satisfies (lpp_integer_assignment rho) formula"
proof -
  let ?rename = "lpp_numeric_rename bindings"
  have ins: "list_all (lpp_check_numeric_endpoint K) inputs"
    and outs: "list_all (lpp_check_numeric_endpoint K) outputs"
    and tests: "list_all2 (lpp_check_numeric_observation K) observations numeric_tests"
    and formula: "formula=lpp_numeric_path_formula inputs outputs numeric_tests bindings"
    using checked by (auto simp: lpp_check_numeric_path_def)
  have input_formula: "IA4.satisfies (lpp_integer_assignment rho) f"
    if member: "endpoint\<in>set inputs" and f: "f\<in>set (lpp_numeric_input_formula ?rename endpoint)" for endpoint f
  proof -
    have check: "lpp_check_numeric_endpoint K endpoint" using ins member by (simp add: list_all_iff)
    have rep: "lp_ieval (fst (snd endpoint)) eta=lpp_integer_value (rho (Pre (fst endpoint)))"
      using inputs member by (cases endpoint) auto
    show ?thesis using lpp_numeric_endpoint_formula_sound[where rho=rho and rename="?rename" and tag=Pre and eta=eta, OF check typed rep] f
      by (cases endpoint) (auto split: if_splits)
  qed
  have output_formula: "IA4.satisfies (lpp_integer_assignment rho) (lpp_numeric_endpoint_formula Post ?rename endpoint)"
    if member: "endpoint\<in>set outputs" for endpoint
  proof -
    have check: "lpp_check_numeric_endpoint K endpoint" using outs member by (simp add: list_all_iff)
    have rep: "lp_ieval (fst (snd endpoint)) eta=lpp_integer_value (rho (Post (fst endpoint)))"
      using outputs member by (cases endpoint) auto
    show ?thesis by (rule lpp_numeric_endpoint_formula_sound[where rho=rho and rename="?rename" and tag=Post and eta=eta, OF check typed rep])
  qed
  have numeric_truth: "list_all (lpp_numeric_condition_holds (rho o ?rename)) numeric_tests"
    using tests observed
  proof (induct rule: list_all2_induct)
    case Nil then show ?case by simp
  next
    case (Cons ob test obs rest)
    have current: "lpp_numeric_condition_holds (rho o ?rename) test"
      by (rule lpp_check_numeric_observation_sound[where eta=eta and rho="rho o ?rename", OF Cons.hyps(1)]) (use Cons.prems typed in auto)
    show ?case using Cons current by (simp add: o_def)
  qed
  show ?thesis using input_formula output_formula numeric_truth
    by (auto simp: formula lpp_numeric_path_formula_def Let_def list_all_iff
      lpp_comparison_typed_assignment lpp_expression_rename_value split: prod.splits)
qed


lemma lpp_numeric_path_formula_typed:
  "IA4.formula (lpp_numeric_path_formula inputs outputs numeric_tests bindings)"
  by (auto simp: lpp_numeric_path_formula_def Let_def list_all_iff
    lpp_comparison_its_type lpp_expression_its_type less_Suc_eq split: prod.splits if_splits)

theorem lpp_checked_numeric_path_step:
  assumes checked: "lpp_check_numeric_path K inputs outputs observations numeric_tests bindings formula"
    and observed: "list_all (lpp_numeric_observation_holds eta) observations"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value
      (lpp_trans_integer pre post middle (lpp_numeric_rename bindings x))"
    and inputs: "\<And>name t e. (name,t,e)\<in>set inputs \<Longrightarrow>
      lp_ieval t eta=lpp_integer_value (pre name)"
    and outputs: "\<And>name t e. (name,t,e)\<in>set outputs \<Longrightarrow>
      lp_ieval t eta=lpp_integer_value (post name)"
    and member: "Transition from to formula\<in>transition_rules system"
    and before: "IA4.satisfies (lpp_integer_assignment pre) (assertion system from)"
    and after: "IA4.satisfies (lpp_integer_assignment post) (assertion system to)"
  shows "(State (lpp_integer_assignment pre) from,State (lpp_integer_assignment post) to)
    \<in>LPPIntegerLTS.transition system"
proof -
  have formula: "IA4.satisfies (lpp_integer_assignment (lpp_trans_integer pre post middle)) formula"
    by (rule lpp_check_numeric_path_sound[where eta=eta, OF checked observed typed])
      (use inputs outputs in auto)
  show ?thesis
    by (rule LPPIntegerLTS.mem_transitionI[OF member],
      rule LPPIntegerLTS.mem_transition_step_TransitionI[where \<gamma>="lpp_integer_assignment middle"])
      (use formula before after in \<open>auto simp: lpp_integer_assignment_typed lpp_pre_post_integer_assignment\<close>)
qed

ML \<open>
val checked = [@{thm lpp_check_numeric_path_sound}, @{thm lpp_checked_numeric_path_step},
  @{thm lpp_numeric_path_formula_typed}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted numeric path dependency" else ();
\<close>
end
