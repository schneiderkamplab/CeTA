theory LP_Cut_SEG_Observed_Invariant
  imports LP_Cut_SEG_Projected_Control
begin

definition lpc_seg_observer_invariant where
  "lpc_seg_observer_invariant filtering is_cont c d inp m ss =
    list_all (\<lambda>e. lp_iproject filtering
      (lpc_seg_runtime_value is_cont c d inp (snd e)) m) ss"

lemma lpc_seg_observer_step:
  fixes m :: "('g,string) term"
  assumes step: "lpc_answer_transition P ss event us"
    and inv: "lpc_seg_observer_invariant filtering is_cont c d inp m ss"
  shows "lpc_seg_observer_invariant filtering is_cont c d inp m us"
  using step inv
  by (cases rule: lpc_answer_transition.cases)
    (auto simp: lpc_seg_observer_invariant_def lpc_seg_runtime_value_def list_all_iff
      lp_ieval_subst[symmetric] intro: lpc_seg_role_projection_subst[simplified]
      dest: subsetD[OF lpc_answer_prune_set_subset])

lemma lpc_seg_observer_subset:
  "set us\<subseteq> set ss \<Longrightarrow> lpc_seg_observer_invariant filtering is_cont c d inp m ss \<Longrightarrow>
    lpc_seg_observer_invariant filtering is_cont c d inp m us"
  by (auto simp: lpc_seg_observer_invariant_def list_all_iff)

lemma lpc_seg_observer_scopes:
  "lpc_seg_observer_invariant filtering is_cont c d inp m (lpc_return_scope_word swaps ss) =
    lpc_seg_observer_invariant filtering is_cont c d inp m ss"
proof (induct swaps arbitrary: ss)
  case Nil then show ?case by simp
next
  case (Cons p swaps)
  show ?case by (cases p)
    (simp only: lpc_return_scope_word.simps Cons.hyps;
      auto simp: lpc_seg_observer_invariant_def list_all_iff)
qed

end
