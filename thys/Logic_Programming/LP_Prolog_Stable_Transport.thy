theory LP_Prolog_Stable_Transport
 imports LP_Prolog_Stable_Context_Initialization
begin

fun lpp_check_stable_comparison_transport where
  "lpp_check_stable_comparison_transport observations mu (LPPOComparison c a b) =
    (lpp_numeric_observation_substitute (LPPOComparison c a b) mu \<in> set observations)"
| "lpp_check_stable_comparison_transport observations mu observation = True"

lemma lpp_stable_transport_observation:
  assumes checked: "lpp_check_stable_comparison_transport observations mu observation"
    and source: "list_all (lpp_stable_observation_holds operation eta) observations"
    and prior: "lpp_evaluation_observation_holds (lpp_stable_scalar_evaluation operation)
      (\<lambda>x. lp_ieval (mu x) eta) observation"
  shows "lpp_stable_observation_holds operation (\<lambda>x. lp_ieval (mu x) eta) observation"
  using checked source prior
  by (cases observation) (auto simp: list_all_iff lpp_stable_observation_substitute[symmetric] lp_ieval_finite_subst)

fun lpp_check_stable_context_transport where
  "lpp_check_stable_context_transport T fs (facts,guards,observations)
      (child_facts,child_guards,child_observations) bindings =
    (lpp_check_evaluation_context_transport T facts guards observations fs
       child_facts child_guards child_observations bindings \<and>
     list_all (lpp_check_stable_comparison_transport observations (lp_cut_instance_subst bindings)) child_observations)"

lemma lpp_stable_context_transport_sound:
  fixes P :: "'v lpp_success_clause list"
    and incoming outgoing :: "'v lpp_source_context"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T P receipts"
    and checked: "lpp_check_stable_context_transport T fs incoming outgoing bindings"
    and source: "lpp_stable_context_holds operation P incoming eta"
  shows "lpp_stable_context_holds operation P outgoing
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
proof -
  obtain facts guards observations where src: "incoming=(facts,guards,observations)"
    by (cases incoming) auto
  obtain child_facts child_guards child_observations where dst:
    "outgoing=(child_facts,child_guards,child_observations)" by (cases outgoing) auto
  have old_check: "lpp_check_evaluation_context_transport T facts guards observations fs
    child_facts child_guards child_observations bindings"
    using checked by (simp add: src dst)
  have old_source: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) P
    (facts,guards,observations) eta"
    using source by (simp add: src lpp_stable_context_holds_def)
  have base: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) P outgoing
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
    unfolding dst
    by (rule lpp_evaluation_context_transport_sound[where E="lpp_stable_scalar_evaluation operation",
      OF _ _ program old_check old_source])
      (auto intro: lpp_stable_evaluation_integer_contract[OF compatible] dest: lpp_stable_scalar_evaluation_ground)
  show ?thesis using base checked source
    by (auto simp: src dst lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff
      intro: lpp_stable_transport_observation[where observations=observations])
qed

lemma lpp_stable_transport_existing_receipt:
  "lpp_check_stable_context_transport T fs incoming outgoing bindings =
    lpp_evaluation_context_transport T fs incoming outgoing bindings"
proof -
  have extra: "lpp_evaluation_observation_check K guards observations
      (lpp_numeric_observation_substitute observation mu) \<Longrightarrow>
      lpp_check_stable_comparison_transport observations mu observation"
    for K guards observations observation mu
    by (cases observation) auto
  show ?thesis
    by (cases incoming; cases outgoing; auto simp: lpp_check_evaluation_context_transport_def Let_def list_all_iff intro: extra)
qed

lemma lpp_stable_existing_transport_sound:
  fixes P :: "'v lpp_success_clause list"
    and incoming outgoing :: "'v lpp_source_context"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T P receipts"
    and checked: "lpp_evaluation_context_transport T fs incoming outgoing bindings"
    and source: "lpp_stable_context_holds operation P incoming eta"
  shows "lpp_stable_context_holds operation P outgoing
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
  by (rule lpp_stable_context_transport_sound[OF compatible program _ source])
    (use checked in \<open>simp only: lpp_stable_transport_existing_receipt\<close>)

ML \<open>
val checked = [@{thm lpp_stable_transport_observation}, @{thm lpp_stable_context_transport_sound},
  @{thm lpp_stable_transport_existing_receipt}, @{thm lpp_stable_existing_transport_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable transport dependency" else ();
\<close>
end
