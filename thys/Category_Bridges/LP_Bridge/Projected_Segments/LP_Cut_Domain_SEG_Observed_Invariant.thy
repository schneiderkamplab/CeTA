theory LP_Cut_Domain_SEG_Observed_Invariant
 imports LP_Cut_Domain_SEG_Projected_Split_Check
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_seg_observer_step:
  fixes m :: "('g,string) term"
  assumes step: "precise_answer_transition P ss event us"
    and inv: "lpc_seg_observer_invariant filtering is_cont c d inp m ss"
  shows "lpc_seg_observer_invariant filtering is_cont c d inp m us"
  using step inv
  by (cases rule: precise_answer_transition.cases)
    (auto simp: lpc_seg_observer_invariant_def lpc_seg_runtime_value_def list_all_iff
      lp_ieval_subst[symmetric] intro: lpc_seg_role_projection_subst[simplified]
      dest: subsetD[OF lpc_answer_prune_set_subset])


end
end
