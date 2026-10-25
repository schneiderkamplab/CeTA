theory LP_Cut_SEG_Projected_Context
  imports LP_Cut_SEG_Projected_Relation
begin

hide_const (open) CPF_Proof_Parser.afs

text \<open>A continuation retains its active child at position zero.
Other positions need only have the finite observations selected by the filter.
No unselected data value is required to be ground.\<close>

lemma lpc_seg_projected_pending:
  assumes af: "afs filtering (f,Suc (length captured)) = AFList (0#map Suc indices)"
    and captured_pr: "list_all2 (\<lambda>i m. i<length captured \<and>
      lp_iproject filtering (captured!i) m) indices ms"
    and child: "lp_iproject filtering t n"
  shows "lp_iproject filtering (LPIFun f (t#captured)) (Fun f (n#ms))"
  by (rule lp_iproject.list[where indices="0#map Suc indices"])
    (use af captured_pr child in \<open>auto simp: list_all2_map1\<close>)

lemma lpc_seg_projected_pending_child:
  fixes filtering :: "'a afs"
  assumes af: "afs filtering (f,Suc (length captured)) = AFList (0#map Suc indices)"
    and observed: "lpc_seg_has_projection filtering (LPIFun f (t#captured))"
  shows "lpc_seg_has_projection filtering t"
proof -
  obtain m :: "('a,string) term" where pr: "lp_iproject filtering (LPIFun f (t#captured)) m"
    using observed by (auto simp: lpc_seg_has_projection_def)
  show ?thesis using pr af
    by (cases rule: lp_iproject.cases)
      (auto simp: lpc_seg_has_projection_def list_all2_Cons1)
qed

lemma lpc_seg_projected_pending_components:
  fixes filtering :: "'a afs"
  assumes af: "afs filtering (f,Suc (length captured)) = AFList (0#map Suc indices)"
    and observed: "lpc_seg_has_projection filtering (LPIFun f (t#captured))"
  obtains n :: "('a,string) term" and ms :: "('a,string) term list" where
    "lp_iproject filtering t n"
    "list_all2 (\<lambda>i m. i<length captured \<and> lp_iproject filtering (captured!i) m) indices ms"
proof -
  obtain m :: "('a,string) term" where pr: "lp_iproject filtering (LPIFun f (t#captured)) m"
    using observed by (auto simp: lpc_seg_has_projection_def)
  show thesis using pr af that
    by (cases rule: lp_iproject.cases)
      (auto simp: list_all2_Cons1 list_all2_map1)
qed

lemma lpc_seg_projected_pending_step:
  fixes filtering :: "'a afs" and ms :: "('a,string) term list"
  assumes af: "afs filtering (f,Suc (length captured)) = AFList (0#map Suc indices)"
    and captured_pr: "list_all2 (\<lambda>i m. i<length captured \<and>
      lp_iproject filtering (captured!i) m) indices ms"
    and edge: "(s,t)\<in>lpc_seg_projected_rel filtering R"
  shows "(LPIFun f (s#captured),LPIFun f (t#captured))\<in>lpc_seg_projected_rel filtering R"
proof -
  obtain a b where left: "lp_iproject filtering s a" and right: "lp_iproject filtering t b"
    and progress: "(a,b)\<in>rstep (af_rule filtering ` R)"
    using edge by (auto simp: lpc_seg_projected_rel_def)
  have l: "lp_iproject filtering (LPIFun f (s#captured)) (Fun f (a#ms))"
    by (rule lpc_seg_projected_pending[OF af captured_pr left])
  have r: "lp_iproject filtering (LPIFun f (t#captured)) (Fun f (b#ms))"
    by (rule lpc_seg_projected_pending[OF af captured_pr right])
  have step: "(Fun f (a#ms),Fun f (b#ms))\<in>rstep (af_rule filtering ` R)"
    using rstep_ctxt[OF progress, of "More f [] Hole ms"] by simp
  show ?thesis using l r step by (auto simp: lpc_seg_projected_rel_def)
qed

lemma lpc_seg_projected_pending_path:
  fixes filtering :: "'a afs" and ms :: "('a,string) term list"
  assumes af: "afs filtering (f,Suc (length captured)) = AFList (0#map Suc indices)"
    and captured_pr: "list_all2 (\<lambda>i m. i<length captured \<and>
      lp_iproject filtering (captured!i) m) indices ms"
    and path: "(s,t)\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
  shows "(LPIFun f (s#captured),LPIFun f (t#captured))\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
  using path
  by (induct rule: rtrancl_induct)
    (auto intro: rtrancl_into_rtrancl lpc_seg_projected_pending_step[OF af captured_pr])

inductive lpc_seg_projection_context ::
  "'f afs \<Rightarrow> (('f,string) lp_iterm \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow> bool"
  for filtering where
  hole: "lpc_seg_projection_context filtering (\<lambda>x. x)"
| frame: "lpc_seg_projection_context filtering A \<Longrightarrow>
    afs filtering (f,Suc (length captured)) = AFList (0#map Suc indices) \<Longrightarrow>
    list_all2 (\<lambda>i m. i<length captured \<and> lp_iproject filtering (captured!i) m) indices (ms::('f,string) term list) \<Longrightarrow>
    lpc_seg_projection_context filtering (\<lambda>x. A (LPIFun f (x#captured)))"

lemma lpc_seg_projection_context_reflect:
  assumes ctx: "lpc_seg_projection_context filtering A"
    and observed: "lpc_seg_has_projection filtering (A t)"
  shows "lpc_seg_has_projection filtering t"
  using ctx observed
  by (induct arbitrary: t rule: lpc_seg_projection_context.induct)
    (auto intro: lpc_seg_projected_pending_child)

lemma lpc_seg_projection_context_step:
  assumes ctx: "lpc_seg_projection_context filtering A"
    and edge: "(s,t)\<in>lpc_seg_projected_rel filtering R"
  shows "(A s,A t)\<in>lpc_seg_projected_rel filtering R"
  using ctx edge
  by (induct arbitrary: s t rule: lpc_seg_projection_context.induct)
    (auto intro: lpc_seg_projected_pending_step)

end
