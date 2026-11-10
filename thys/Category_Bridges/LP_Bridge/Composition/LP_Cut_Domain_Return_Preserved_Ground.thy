theory LP_Cut_Domain_Return_Preserved_Ground
 imports LP_Cut_Domain_Return_Split_Check
begin

context cut_runtime_domain
begin

lemma precise_answer_ground_env_preserved:
  assumes step: "precise_answer_transition P ss event us"
    and known: "list_all (\<lambda>e. \<forall>x\<in>G. lp_seg_ground (snd e x)) ss"
  shows "list_all (\<lambda>e. \<forall>x\<in>G. lp_seg_ground (snd e x)) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> (\<forall>x\<in>G. lp_seg_ground (eta x)))"
  using step known
  by (cases rule: precise_answer_transition.cases)
    (auto simp: list_all_iff lp_seg_ground_subst
      dest: subsetD[OF lpc_answer_prune_set_subset])

lemma precise_actual_return_preserves_ground_env:
  assumes actual: "precise_actual_return P ss eta"
    and known: "list_all (\<lambda>e. \<forall>x\<in>G. lp_seg_ground (snd e x)) ss"
  shows "\<forall>x\<in>G. lp_seg_ground (eta x)"
proof -
  obtain us tail where path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some eta) tail"
    using actual by (auto simp: precise_actual_return_def)
  have preserved: "list_all (\<lambda>e. \<forall>x\<in>G. lp_seg_ground (snd e x)) us"
    using path known
    by (induct rule: rtrancl_induct)
      (auto simp: precise_answer_steps_def dest: precise_answer_ground_env_preserved)
  show ?thesis using precise_answer_ground_env_preserved[OF event preserved] by simp
qed


end
end
