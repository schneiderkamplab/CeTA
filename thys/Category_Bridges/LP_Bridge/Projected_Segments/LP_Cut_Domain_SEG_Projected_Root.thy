theory LP_Cut_Domain_SEG_Projected_Root
 imports LP_Cut_Domain_SEG_Projected_Region
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

definition precise_seg_projected_root_rep where
  "precise_seg_projected_root_rep filtering roots Fs is_cont c d ss t ret =
    (\<exists>i eta A. i<length roots \<and> lpc_free_knowledge (set (Fs!i)) eta \<and>
      knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
        (lpcn_guards (lpcsr_node (roots!i))) eta \<and>
      lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta) \<and>
      lpc_seg_projection_context filtering A \<and>
      ss=lpc_return_eval eta (lpc_seg_root_state (roots!i)) \<and>
      t=A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta) \<and>
      ret=(\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output (roots!i)) rho)))"


lemma precise_seg_projected_root_repI:
  assumes index: "i<length roots"
    and known: "knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
      (lpcn_guards (lpcsr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and observed: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta)"
    and ambient: "lpc_seg_projection_context filtering A"
  shows "precise_seg_projected_root_rep filtering roots Fs is_cont c d
    (lpc_return_eval eta (lpc_seg_root_state (roots!i)))
    (A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output (roots!i)) rho))"
  unfolding precise_seg_projected_root_rep_def
  by (rule exI[of _ i], rule exI[of _ eta], rule exI[of _ A])
    (use index known free observed ambient in simp)


theorem precise_seg_projected_graph_contract:
  fixes filtering :: "'g afs"
  assumes sn: "SN (rstep (af_rule filtering ` R))"
    and rep: "precise_seg_projected_root_rep filtering roots Fs is_cont c d ss t ret"
    and local: "\<And>i eta A. i<length roots \<Longrightarrow>
      knowledge (set (lpcn_ground (lpcsr_node (roots!i)))) (lpcn_guards (lpcsr_node (roots!i))) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta) \<Longrightarrow>
      lpc_seg_projection_context filtering A \<Longrightarrow>
      (\<And>us v out. (A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta),v)
        \<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
        precise_seg_projected_root_rep filtering roots Fs is_cont c d us v out \<Longrightarrow>
        precise_return_contract P us (lpc_seg_projected_rel filtering R) v out) \<Longrightarrow>
      precise_return_contract P (lpc_return_eval eta (lpc_seg_root_state (roots!i))) (lpc_seg_projected_rel filtering R)
        (A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta))
        (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output (roots!i)) rho))"
  shows "precise_return_contract P ss (lpc_seg_projected_rel filtering R) t ret"
proof -
  have observed: "lpc_seg_has_projection filtering t"
    using rep lpc_seg_projection_context_observed by (auto simp: precise_seg_projected_root_rep_def)
  obtain m :: "('g,string) term" where measured: "lp_iproject filtering t m"
    using observed by (auto simp: lpc_seg_has_projection_def)
  have terminating: "SN_on (lpc_seg_projected_rel filtering R) {t}"
    by (rule lpc_seg_projected_SN[OF SN_on_subset2[OF subset_UNIV sn] measured])
  show ?thesis
    by (rule precise_return_contract_modular[where rep="precise_seg_projected_root_rep filtering roots Fs is_cont c d", OF terminating rep])
      (use local in \<open>auto simp: precise_seg_projected_root_rep_def\<close>)
qed


end
end
