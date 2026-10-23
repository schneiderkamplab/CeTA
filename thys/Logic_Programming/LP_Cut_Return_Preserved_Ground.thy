theory LP_Cut_Return_Preserved_Ground
  imports LP_Cut_Return_Actual LP_Cut_Return_Interface
begin

text \<open>Ground inputs survive every active substitution and saved
alternative. Unlike successful-answer analysis through a cut-erased program,
this invariant needs no restriction on meta-calls and proves no new output
groundness. It applies only to actual successful returns.\<close>

lemma lpc_answer_prune_preserves_env_property:
  "list_all (\<lambda>x. F (snd x)) ss \<Longrightarrow>
   list_all (\<lambda>x. F (snd x)) (lpc_answer_prune m ss)"
  by (induct ss) (auto split: prod.splits lp_cut_entry.splits)

lemma lpc_answer_prune_set_subset:
  "set (lpc_answer_prune m ss) \<subseteq> set ss"
  by (induct ss) (auto simp: subset_iff split: prod.splits lp_cut_entry.splits if_splits)

lemma lpc_answer_ground_env_preserved:
  assumes step: "lpc_answer_transition P ss event us"
    and known: "list_all (\<lambda>e. \<forall>x\<in>G. lp_seg_ground (snd e x)) ss"
  shows "list_all (\<lambda>e. \<forall>x\<in>G. lp_seg_ground (snd e x)) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> (\<forall>x\<in>G. lp_seg_ground (eta x)))"
  using step known
  by (cases rule: lpc_answer_transition.cases)
    (auto simp: list_all_iff lp_seg_ground_subst
      dest: subsetD[OF lpc_answer_prune_set_subset])

lemma lpc_actual_return_preserves_ground_env:
  assumes actual: "lpc_actual_return P ss eta"
    and known: "list_all (\<lambda>e. \<forall>x\<in>G. lp_seg_ground (snd e x)) ss"
  shows "\<forall>x\<in>G. lp_seg_ground (eta x)"
proof -
  obtain us tail where path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some eta) tail"
    using actual by (auto simp: lpc_actual_return_def)
  have preserved: "list_all (\<lambda>e. \<forall>x\<in>G. lp_seg_ground (snd e x)) us"
    using path known
    by (induct rule: rtrancl_induct)
      (auto simp: lpc_answer_steps_def dest: lpc_answer_ground_env_preserved)
  show ?thesis using lpc_answer_ground_env_preserved[OF event preserved] by simp
qed

end
