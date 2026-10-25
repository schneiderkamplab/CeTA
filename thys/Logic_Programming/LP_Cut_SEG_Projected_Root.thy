theory LP_Cut_SEG_Projected_Root
  imports LP_Cut_SEG_Projected_Region LP_Cut_SEG_Free_Root_Representation
begin

hide_const (open) CPF_Proof_Parser.rstep

definition lpc_seg_projected_root_rep where
  "lpc_seg_projected_root_rep filtering roots Fs is_cont c d ss t ret =
    (\<exists>i eta A. i<length roots \<and> lpc_free_knowledge (set (Fs!i)) eta \<and>
      lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
        (lpcn_guards (lpcsr_node (roots!i))) eta \<and>
      lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta) \<and>
      lpc_seg_projection_context filtering A \<and>
      ss=lpc_return_eval eta (lpc_seg_root_state (roots!i)) \<and>
      t=A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta) \<and>
      ret=(\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output (roots!i)) rho)))"

lemma lpc_seg_projected_root_repI:
  assumes index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
      (lpcn_guards (lpcsr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and observed: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta)"
    and ambient: "lpc_seg_projection_context filtering A"
  shows "lpc_seg_projected_root_rep filtering roots Fs is_cont c d
    (lpc_return_eval eta (lpc_seg_root_state (roots!i)))
    (A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output (roots!i)) rho))"
  unfolding lpc_seg_projected_root_rep_def
  by (rule exI[of _ i], rule exI[of _ eta], rule exI[of _ A])
    (use index known free observed ambient in simp)

lemma lpc_seg_projection_context_observed:
  fixes filtering :: "'f afs"
  assumes ctx: "lpc_seg_projection_context filtering A"
    and initial: "lpc_seg_has_projection filtering t"
  shows "lpc_seg_has_projection filtering (A t)"
  using ctx initial
proof (induct arbitrary: t rule: lpc_seg_projection_context.induct)
  case hole then show ?case by simp
next
  case (frame A f captured indices ms)
  obtain n :: "('f,string) term" where child: "lp_iproject filtering t n"
    using frame.prems by (auto simp: lpc_seg_has_projection_def)
  have pr: "lp_iproject filtering (LPIFun f (t#captured)) (Fun f (n#ms))"
    by (rule lpc_seg_projected_pending[OF frame.hyps(3,4) child])
  have observed: "lpc_seg_has_projection filtering (LPIFun f (t#captured))"
    using pr by (auto simp: lpc_seg_has_projection_def)
  show ?case using frame.hyps(2)[OF observed] by simp
qed

theorem lpc_seg_projected_graph_contract:
  fixes filtering :: "'g afs"
  assumes sn: "SN (rstep (af_rule filtering ` R))"
    and rep: "lpc_seg_projected_root_rep filtering roots Fs is_cont c d ss t ret"
    and local: "\<And>i eta A. i<length roots \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i)))) (lpcn_guards (lpcsr_node (roots!i))) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta) \<Longrightarrow>
      lpc_seg_projection_context filtering A \<Longrightarrow>
      (\<And>us v out. (A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta),v)
        \<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
        lpc_seg_projected_root_rep filtering roots Fs is_cont c d us v out \<Longrightarrow>
        lpc_return_contract P us (lpc_seg_projected_rel filtering R) v out) \<Longrightarrow>
      lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state (roots!i))) (lpc_seg_projected_rel filtering R)
        (A (lpc_seg_runtime_value is_cont c d (lpcsr_input (roots!i)) eta))
        (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output (roots!i)) rho))"
  shows "lpc_return_contract P ss (lpc_seg_projected_rel filtering R) t ret"
proof -
  have observed: "lpc_seg_has_projection filtering t"
    using rep lpc_seg_projection_context_observed by (auto simp: lpc_seg_projected_root_rep_def)
  obtain m :: "('g,string) term" where measured: "lp_iproject filtering t m"
    using observed by (auto simp: lpc_seg_has_projection_def)
  have terminating: "SN_on (lpc_seg_projected_rel filtering R) {t}"
    by (rule lpc_seg_projected_SN[OF SN_on_subset2[OF subset_UNIV sn] measured])
  show ?thesis
    by (rule lpc_return_contract_modular[where rep="lpc_seg_projected_root_rep filtering roots Fs is_cont c d", OF terminating rep])
      (use local in \<open>auto simp: lpc_seg_projected_root_rep_def\<close>)
qed

lemma lpc_seg_projection_context_equal:
  fixes filtering :: "'f afs" and m :: "('f,string) term"
  assumes ctx: "lpc_seg_projection_context filtering A"
    and left: "lp_iproject filtering s m"
    and right: "lp_iproject filtering t m"
  shows "\<exists>n::('f,string) term. lp_iproject filtering (A s) n \<and> lp_iproject filtering (A t) n"
  using ctx left right
proof (induct arbitrary: s t m rule: lpc_seg_projection_context.induct)
  case hole then show ?case by auto
next
  case (frame A f captured indices ms)
  have l: "lp_iproject filtering (LPIFun f (s#captured)) (Fun f (m#ms))"
    by (rule lpc_seg_projected_pending[OF frame.hyps(3,4) frame.prems(1)])
  have r: "lp_iproject filtering (LPIFun f (t#captured)) (Fun f (m#ms))"
    by (rule lpc_seg_projected_pending[OF frame.hyps(3,4) frame.prems(2)])
  show ?case using frame.hyps(2)[OF l r] by simp
qed

lemma lpc_seg_projected_replace_left:
  fixes filtering :: "'f afs" and m :: "('f,string) term"
  assumes left: "lp_iproject filtering s m"
    and right: "lp_iproject filtering t m"
    and edge: "(A t,u)\<in>lpc_seg_projected_rel filtering R"
    and ctx: "lpc_seg_projection_context filtering A"
  shows "(A s,u)\<in>lpc_seg_projected_rel filtering R"
proof -
  obtain n :: "('f,string) term" where l: "lp_iproject filtering (A s) n" and r: "lp_iproject filtering (A t) n"
    using lpc_seg_projection_context_equal[OF ctx left right] by blast
  obtain a b where a: "lp_iproject filtering (A t) a" and b: "lp_iproject filtering u b"
    and progress: "(a,b)\<in>rstep (af_rule filtering ` R)"
    using edge by (auto simp: lpc_seg_projected_rel_def)
  have eq: "a=n" by (rule lp_iproject_unique[OF a r])
  show ?thesis using l b progress eq by (auto simp: lpc_seg_projected_rel_def)
qed

end
