theory LP_Cut_SEG_Free_Root_Representation
  imports LP_Cut_SEG_Root_Representation LP_Cut_SEG_Free_Control
begin

definition lpc_seg_free_root_rep where
  "lpc_seg_free_root_rep roots Fs is_cont c d ss t ret =
    (\<exists>i eta A. i<length roots \<and> lpc_free_knowledge (set (Fs!i)) eta \<and>
      lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
        (lpcn_guards (lpcsr_node (roots!i))) eta \<and>
      lp_seg_ground (lp_ieval (lpcsr_input (roots!i)) eta) \<and>
      ss=lpc_return_eval eta (lpc_seg_root_state (roots!i)) \<and>
      t=A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle> \<and>
      ret=(\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output (roots!i)) rho\<rangle>))"

lemma lpc_seg_free_root_repI:
  assumes index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
      (lpcn_guards (lpcsr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input (roots!i)) eta)"
  shows "lpc_seg_free_root_rep roots Fs is_cont c d
    (lpc_return_eval eta (lpc_seg_root_state (roots!i)))
    (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output (roots!i)) rho\<rangle>)"
  unfolding lpc_seg_free_root_rep_def
  by (rule exI[of _ i], rule exI[of _ eta], rule exI[of _ A])
    (use index known free finite in simp)

lemma lpc_seg_free_root_lower:
  assumes lower: "\<And>vs v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow>
      lpc_seg_free_root_rep roots Fs is_cont c d vs v out \<Longrightarrow> lpc_return_contract P vs R v out"
    and index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
      (lpcn_guards (lpcsr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input (roots!i)) eta)"
    and strict: "(t,A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>)\<in>R\<^sup>+"
  shows "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state (roots!i))) R
    (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output (roots!i)) rho\<rangle>)"
  by (rule lower[OF strict lpc_seg_free_root_repI[OF index known free finite]])

end
