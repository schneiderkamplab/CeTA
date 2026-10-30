theory LP_Prolog_Evaluation_Context
  imports LP_Prolog_Guarded_Ground_Return LP_Prolog_Context_Free_Link
begin

text \<open>The existing context representation can be interpreted with an
explicit evaluation relation. Integer deductions still require the shared
conditional transfer checker; a successful finite evaluation alone supplies
finite groundness, not integer typing.\<close>

fun lpp_evaluation_observation_holds where
  "lpp_evaluation_observation_holds E eta (LPPOGround t) = lp_seg_ground (lp_ieval t eta)"
| "lpp_evaluation_observation_holds E eta (LPPOShape G shape t) = lp_return_shape_holds G shape (lp_ieval t eta)"
| "lpp_evaluation_observation_holds E eta (LPPOInteger t) = lpp_is_integer (lp_ieval t eta)"
| "lpp_evaluation_observation_holds E eta (LPPOEvaluation e t) = E (lp_ieval e eta) (lp_ieval t eta)"
| "lpp_evaluation_observation_holds E eta (LPPOComparison c a b) =
    lpp_finite_compare_outcome c (lp_ieval a eta) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"

lemma lpp_evaluation_observation_legacy:
  "lpp_evaluation_observation_holds lpp_integer_result eta observation =
    lpp_numeric_observation_holds eta observation"
  by (cases observation) simp_all

definition lpp_evaluation_context_holds where
  "lpp_evaluation_context_holds E P context eta = (case context of (facts,guards,observations) \<Rightarrow>
    list_all (\<lambda>b. lpp_guarded_success P E (lpp_success_atom_eval b eta)) facts \<and>
    list_all (lpp_success_guard_holds E eta) guards \<and>
    list_all (lpp_evaluation_observation_holds E eta) observations)"

lemma lpp_evaluation_context_legacy:
  "lpp_evaluation_context_holds lpp_integer_result P context eta = lpp_source_context_holds P context eta"
  by (cases "context") (simp add: lpp_evaluation_context_holds_def lpp_path_context_holds_def lpp_evaluation_observation_legacy list_all_iff)

lemma lpp_evaluation_observation_substitute:
  "lpp_evaluation_observation_holds E eta (lpp_numeric_observation_substitute observation mu) =
    lpp_evaluation_observation_holds E (\<lambda>x. lp_ieval (mu x) eta) observation"
  by (cases observation) (simp_all add: lp_ieval_finite_subst)

lemma lpp_evaluation_context_substitute:
  "lpp_evaluation_context_holds E P (lpp_source_context_subst context mu) eta =
    lpp_evaluation_context_holds E P context (\<lambda>x. lp_ieval (mu x) eta)"
  by (cases "context") (simp add: lpp_evaluation_context_holds_def
    list_all_iff lpp_success_atom_subst_eval
    lpp_success_guard_subst_eval lpp_evaluation_observation_substitute)

lemma lpp_evaluation_observation_subst:
  assumes stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and observed: "lpp_evaluation_observation_holds E eta observation"
  shows "lpp_evaluation_observation_holds E (\<lambda>x. lp_isubst (eta x) sigma) observation"
  using observed by (cases observation)
    (auto simp: lp_ieval_subst[symmetric] lp_seg_ground_subst intro: stable lp_seg_ground_subst lpp_is_integer_subst lpp_finite_comparison_subst lp_return_shape_subst)

lemma lpp_evaluation_context_integer:
  fixes P :: "'v lpp_success_clause list" and facts :: "'v lpp_success_atom list"
  assumes contract: "lpp_eval_integer_contract TYPE('v) E"
    and program: "lpp_check_transfer_program T P receipts"
    and checked: "lpp_check_operation_context T facts guards fs K"
    and observed: "lpp_evaluation_context_holds E P (facts,guards,observations) eta"
  shows "lpp_integer_known K eta"
proof -
  have path: "lpp_check_path_types T facts guards fs"
    using checked by (simp add: lpp_check_operation_context_def)
  have guards: "list_all (lpp_success_guard_holds E eta) guards"
    and facts: "list_all (lpp_guarded_success P E) (map (\<lambda>b. lpp_success_atom_eval b eta) facts)"
    using observed by (auto simp: lpp_evaluation_context_holds_def list_all_iff)
  have known: "lpp_integer_known (map lpp_transfer_variable fs) eta"
    by (rule lpp_check_path_types_sound[OF program path guards facts contract])
  show ?thesis using known checked
    by (auto simp: lpp_check_operation_context_def lpp_integer_known_def list_all_iff)
qed

lemma lpp_evaluation_observation_ground:
  assumes evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and observed: "lpp_evaluation_observation_holds E eta observation"
  shows "\<forall>x\<in>lpp_observation_ground_vars observation. lp_seg_ground (eta x)"
  using observed by (cases observation)
    (auto simp: lp_seg_ground_eval lpp_finite_compare_outcome_def
      dest: evaluation lpp_integer_ground_vars lp_return_shape_ground_vars_sound)


text \<open>Integer entailments in a link carry the same independently checked
path-type derivation as a source operation. All other observations retain their
original expression, result and bindings.\<close>

definition lpp_context_integer_from where
  "lpp_context_integer_from K guards t =
    (t=lpp_integer_term (lpp_context_literal_candidate t) \<or>
     LPPSInteger t\<in>set guards \<or>
     (\<exists>x\<in>set K. t=Var x))"

lemma lpp_context_integer_from_sound:
  assumes checked: "lpp_context_integer_from K guards t"
    and known: "lpp_integer_known K eta"
    and guards: "list_all (lpp_success_guard_holds E eta) guards"
  shows "lpp_is_integer (lp_ieval t eta)"
proof -
  have literal: "t=lpp_integer_term (lpp_context_literal_candidate t) \<Longrightarrow> lpp_is_integer (lp_ieval t eta)"
    by (metis lpp_integer_literal_eval lpp_is_integer_def)
  show ?thesis using checked known guards literal
    by (auto simp: lpp_context_integer_from_def lpp_integer_known_def list_all_iff lpp_is_integer_def)
qed

fun lpp_evaluation_guard_check where
  "lpp_evaluation_guard_check K guards (LPPSInteger t) = lpp_context_integer_from K guards t"
| "lpp_evaluation_guard_check K guards (LPPSOpaque t) = True"
| "lpp_evaluation_guard_check K guards g = (g\<in>set guards)"

lemma lpp_evaluation_observation_shape_facts:
  assumes held: "lpp_evaluation_observation_holds E eta observation"
  shows "lp_return_shape_known G (lpp_observation_shape_facts G observation) eta"
proof (cases observation)
  case (LPPOShape H shape t)
  have observed: "lp_return_shape_holds H shape (lp_ieval t eta)"
    using held LPPOShape by simp
  have facts: "lp_return_facts_valid H eta (lp_return_shape_facts 16 H shape t)"
    by (rule lp_return_shape_facts_sound[OF observed])
  show ?thesis
  proof (cases "G=H")
    case False
    then show ?thesis by (simp add: LPPOShape lp_return_shape_known_def)
  next
    case True
    show ?thesis
    proof (cases "lp_return_shape_facts 16 H shape t")
      case None
      then show ?thesis using True by (simp add: LPPOShape lp_return_shape_known_def)
    next
      case (Some known)
      have known: "lp_return_shape_known H known eta"
        using facts[unfolded Some] by (simp add: lp_return_facts_valid_def)
      show ?thesis using known True Some by (simp add: LPPOShape)
    qed
  qed
qed (simp_all add: lp_return_shape_known_def)

lemma lpp_evaluation_observations_shape_facts:
  "list_all (lpp_evaluation_observation_holds E eta) observations \<Longrightarrow>
    lp_return_shape_known G (lpp_observations_shape_facts G observations) eta"
  using lpp_evaluation_observation_shape_facts
  by (fastforce simp: lpp_observations_shape_facts_def lp_return_shape_known_def list_all_iff)

fun lpp_evaluation_observation_check where
  "lpp_evaluation_observation_check K guards observations (LPPOGround t) =
    (vars_term t \<subseteq> lpp_observations_ground observations)"
| "lpp_evaluation_observation_check K guards observations (LPPOShape G shape t) =
    (LPPOShape G shape t\<in>set observations \<or>
      lp_return_shape_check 16 G (lpp_observations_shape_facts G observations) shape t)"
| "lpp_evaluation_observation_check K guards observations (LPPOInteger t) = lpp_context_integer_from K guards t"
| "lpp_evaluation_observation_check K guards observations observation = (observation\<in>set observations)"

lemma lpp_evaluation_guard_check_sound:
  "lpp_evaluation_guard_check K guards g \<Longrightarrow>
   lpp_integer_known K eta \<Longrightarrow>
   list_all (lpp_success_guard_holds E eta) guards \<Longrightarrow>
   lpp_success_guard_holds E eta g"
  by (cases g) (auto simp: list_all_iff intro: lpp_context_integer_from_sound)

lemma lpp_evaluation_observation_check_sound:
  assumes evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and checked: "lpp_evaluation_observation_check K guards observations observation"
    and known: "lpp_integer_known K eta"
    and guards: "list_all (lpp_success_guard_holds E eta) guards"
    and observations: "list_all (lpp_evaluation_observation_holds E eta) observations"
  shows "lpp_evaluation_observation_holds E eta observation"
proof -
  have ground: "\<forall>x\<in>lpp_observations_ground observations. lp_seg_ground (eta x)"
    using lpp_evaluation_observation_ground[OF evaluation] observations
    by (auto simp: lpp_observations_ground_def list_all_iff)
  have shapes: "lp_return_shape_holds G shape (lp_ieval t eta)"
    if "lp_return_shape_check 16 G (lpp_observations_shape_facts G observations) shape t" for G shape t
    by (rule lp_return_shape_check_sound[OF that lpp_evaluation_observations_shape_facts[OF observations]])
  show ?thesis using checked known guards observations ground
    by (cases observation) (auto simp: lp_seg_ground_eval list_all_iff intro: shapes lpp_context_integer_from_sound)
qed

definition lpp_check_evaluation_context_transport where
  "lpp_check_evaluation_context_transport T facts guards observations fs child_facts child_guards child_observations bindings =
    (let K=map lpp_transfer_variable fs; mu=lp_cut_instance_subst bindings in
      lpp_check_operation_context T facts guards fs K \<and>
      list_all (\<lambda>b. lpp_success_atom_subst b mu\<in>set facts) child_facts \<and>
      list_all (\<lambda>g. lpp_evaluation_guard_check K guards (lpp_success_guard_subst g mu)) child_guards \<and>
      list_all (\<lambda>observation. lpp_evaluation_observation_check K guards observations
        (lpp_numeric_observation_substitute observation mu)) child_observations)"

lemma lpp_evaluation_context_transport_sound:
  fixes P :: "'v lpp_success_clause list" and facts :: "'v lpp_success_atom list"
  assumes contract: "lpp_eval_integer_contract TYPE('v) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T P receipts"
    and checked: "lpp_check_evaluation_context_transport T facts guards observations fs
      child_facts child_guards child_observations bindings"
    and source: "lpp_evaluation_context_holds E P (facts,guards,observations) eta"
  shows "lpp_evaluation_context_holds E P (child_facts,child_guards,child_observations)
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
proof -
  let ?K="map lpp_transfer_variable fs"
  have typing: "lpp_check_operation_context T facts guards fs ?K"
    using checked by (simp add: lpp_check_evaluation_context_transport_def Let_def)
  have known: "lpp_integer_known ?K eta"
    by (rule lpp_evaluation_context_integer[OF contract program typing source])
  have guards: "list_all (lpp_success_guard_holds E eta) guards"
    and observations: "list_all (lpp_evaluation_observation_holds E eta) observations"
    using source by (auto simp: lpp_evaluation_context_holds_def)
  show ?thesis using checked source
    lpp_evaluation_guard_check_sound[OF _ known guards]
    lpp_evaluation_observation_check_sound[OF evaluation _ known guards observations]
    by (auto simp: lpp_check_evaluation_context_transport_def lpp_evaluation_context_holds_def
      Let_def list_all_iff lpp_success_atom_subst_eval[symmetric]
      lpp_success_guard_subst_eval[symmetric] lpp_evaluation_observation_substitute[symmetric])
qed

ML \<open>
val checked = [@{thm lpp_evaluation_context_transport_sound}, @{thm lpp_evaluation_context_legacy}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted evaluation-context transport dependency" else ();
\<close>
end
