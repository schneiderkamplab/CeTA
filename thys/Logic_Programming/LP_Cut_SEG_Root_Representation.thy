theory LP_Cut_SEG_Root_Representation
  imports LP_Cut_SEG_Context_Region LP_Cut_SEG_Split_Lower
begin

record 'f lpc_seg_root =
  lpcsr_node :: "'f lpc_node"
  lpcsr_input :: "'f lpc_term"
  lpcsr_output :: "('f lp_cut_symbol,nat) term"

definition lpc_seg_root_state where
  "lpc_seg_root_state entry_root = map (\<lambda>e. (e,map Var (lpcn_vars (lpcsr_node entry_root))))
    (lpcn_state (lpcsr_node entry_root))"

definition lpc_seg_root_rep where
  "lpc_seg_root_rep roots is_cont c d ss t ret =
    (\<exists>i eta A. i<length roots \<and>
      lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
        (lpcn_guards (lpcsr_node (roots!i))) eta \<and>
      lp_seg_ground (lp_ieval (lpcsr_input (roots!i)) eta) \<and>
      ss=lpc_return_eval eta (lpc_seg_root_state (roots!i)) \<and>
      t=A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle> \<and>
      ret=(\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output (roots!i)) rho\<rangle>))"

lemma lpc_seg_root_repI:
  assumes index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
      (lpcn_guards (lpcsr_node (roots!i))) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input (roots!i)) eta)"
  shows "lpc_seg_root_rep roots is_cont c d
    (lpc_return_eval eta (lpc_seg_root_state (roots!i)))
    (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output (roots!i)) rho\<rangle>)"
  unfolding lpc_seg_root_rep_def
  by (rule exI[of _ i], rule exI[of _ eta], rule exI[of _ A])
    (use index known finite in simp)

lemma lpc_seg_root_lower:
  assumes lower: "\<And>vs v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow>
      lpc_seg_root_rep roots is_cont c d vs v out \<Longrightarrow> lpc_return_contract P vs R v out"
    and index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
      (lpcn_guards (lpcsr_node (roots!i))) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input (roots!i)) eta)"
    and strict: "(t,A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>)\<in>R\<^sup>+"
  shows "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state (roots!i))) R
    (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output (roots!i)) rho\<rangle>)"
  by (rule lower[OF strict lpc_seg_root_repI[OF index known finite]])

end
