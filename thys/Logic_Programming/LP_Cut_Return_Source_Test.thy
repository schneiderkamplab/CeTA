theory LP_Cut_Return_Source_Test
  imports LP_Cut_Return_Source
begin

lemma attachment_keeps_saved_environments:
  "lpc_attach [LPCAtom (Var x)] [(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)] =
    [LPCGoals [LPCFail,LPCAtom (\<eta> x)],LPCGoals [LPCAtom (\<nu> x)]]"
  by simp

lemma failed_attachment_restores_saved_environment:
  "(lpc_attach [LPCAtom (Var x)] [(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)],
    [LPCGoals [LPCAtom (\<nu> x)]])\<in>lp_cut_mgu_source P"
  by (rule lp_cut_mgu_source.admin) simp

lemma success_boundary_is_not_active:
  "\<not> lpc_prefix_active [(LPCGoals [],\<eta>)]"
  by simp

lemma empty_clause_is_not_active:
  "\<not> lpc_prefix_active [(LPCClause [] c m,\<eta>)]"
  by simp

lemma success_boundary_starts_continuation:
  "(lpc_attach [LPCTrue] [(LPCGoals [],\<eta>)],[LPCGoals []])\<in>lp_cut_mgu_source P"
  by (rule lp_cut_mgu_source.admin) simp

lemma success_boundary_cannot_be_silent_prefix_step:
  "\<not> lpc_answer_transition P [(LPCGoals [],\<eta>)] None tt"
  by (simp add: lpc_answer_success_preserves_alternatives)

lemma ordered_scope_good:
  "lpc_owned_stack {} [LPCGoals [LPCCut 1,LPCCut 2],LPCBarrier 1,LPCBarrier 2]"
  by simp

lemma ordered_scope_removed_inner_rejected:
  "\<not> lpc_owned_stack {} [LPCGoals [LPCCut 2,LPCCut 1],LPCBarrier 1,LPCBarrier 2]"
  by simp

lemma unowned_cut_rejected:
  "\<not> lpc_owned_stack {} [LPCGoals [LPCCut 1]]"
  by simp

lemma external_cut_allowed:
  "lpc_owned_stack {1} [LPCGoals [LPCCut 1]]"
  by simp

lemma external_scope_collision_detected:
  "{1}\<inter>set (lpc_barrier_ids [LPCBarrier 1]) \<noteq> {}"
  by simp

lemma caller_cut_discards_prefix_alternatives:
  "(lpc_attach [LPCCut 7] [(LPCGoals [],\<eta>),(LPCGoals [LPCFail],\<nu>),(LPCBarrier 3,\<rho>)],
    [LPCGoals []])\<in>lp_cut_mgu_source P"
  by (rule lp_cut_mgu_source.admin) simp

lemma local_cut_keeps_caller:
  "(LPCGoals [LPCCut 3]#LPCBarrier 3#caller,
    LPCGoals []#LPCBarrier 3#caller)\<in>lp_cut_mgu_source P"
  by (rule lp_cut_mgu_source.admin) simp

lemma truth_prefix_return_contract:
  "lpc_return_contract P [(LPCGoals [LPCTrue],\<eta>)] {} () (\<lambda>_. ())"
proof -
  let ?rep = "\<lambda>ss u. ss=[] \<or> ss=[(LPCGoals [],\<eta>)] \<or> ss=[(LPCGoals [LPCTrue],\<eta>)]"
  have graph: "lpc_return_graph_valid P {} ?rep (\<lambda>_. ()) (\<lambda>ss. lp_cut_weight (map fst ss))"
    unfolding lpc_return_graph_valid_def
    by (auto simp: lp_cut_weight_def elim: lpc_answer_transition.cases)
  show ?thesis by (rule lpc_return_graph_contract[OF graph]) auto
qed

lemma source_attachment_with_caller_cut:
  assumes program: "lp_cut_source_program P"
  shows "SN_on (lp_cut_mgu_source P) {[LPCGoals [LPCTrue,LPCCut 7,LPCTrue]]}"
proof -
  have empty: "SN_on (lp_cut_mgu_source P) {[]}"
    by (rule step_reflects_SN_on) (auto elim: lp_cut_mgu_source.cases)
  have successful: "SN_on (lp_cut_mgu_source P) {[LPCGoals []]}"
    by (rule step_reflects_SN_on) (use empty in \<open>auto elim: lp_cut_mgu_source.cases\<close>)
  have truth: "SN_on (lp_cut_mgu_source P) {[LPCGoals [LPCTrue]]}"
    by (rule step_reflects_SN_on) (use successful in \<open>auto elim: lp_cut_mgu_source.cases\<close>)
  have cut: "SN_on (lp_cut_mgu_source P) {[LPCGoals [LPCCut 7,LPCTrue]]}"
    by (rule step_reflects_SN_on) (use truth in \<open>auto elim: lp_cut_mgu_source.cases\<close>)
  show ?thesis using lpc_cut_prefix_return_contract_SN[OF program truth_prefix_return_contract,
      where rest="[LPCCut 7,LPCTrue]"] cut by simp
qed

end
