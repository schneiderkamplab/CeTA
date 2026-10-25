theory LP_Cut_SEG_Projected_Call
  imports LP_Cut_SEG_Projected_Child
begin

hide_const (open) CPF_Proof_Parser.afs

definition lpc_seg_projected_continuation_filter where
  "lpc_seg_projected_continuation_filter filtering f n =
    (case afs filtering (f,n) of AFList (0#is) \<Rightarrow> list_all (\<lambda>i. i>0) is | _ \<Rightarrow> False)"

lemma lpc_seg_projected_continuation_filterD:
  assumes "lpc_seg_projected_continuation_filter filtering f n"
  obtains indices where "afs filtering (f,n)=AFList (0#map Suc indices)"
proof -
  obtain js where af: "afs filtering (f,n)=AFList (0#js)" and positive: "list_all (\<lambda>i. i>0) js"
    using assms by (auto simp: lpc_seg_projected_continuation_filter_def split: af_entry.splits list.splits nat.splits)
  have eq: "map Suc (map (\<lambda>i. i-1) js)=js"
    using positive by (induct js) auto
  show thesis by (rule that[of "map (\<lambda>i. i-1) js"]) (simp only: eq af)
qed

theorem lpc_seg_projected_call:
  fixes filtering :: "'g afs"
  assumes checked: "lpc_seg_check_projected_pair filtering 1 2 is_cont c d R l (Fun u (child#captured))"
    and cont: "is_cont u"
    and filter: "lpc_seg_projected_continuation_filter filtering (c u) (Suc (length captured))"
    and observed: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d l eta)"
    and ambient: "lpc_seg_projection_context filtering A"
  obtains indices and ms :: "('g,string) term list" where
    "afs filtering (c u,Suc (length captured))=AFList (0#map Suc indices)"
    "list_all2 (\<lambda>i m. i<length captured \<and>
      lp_iproject filtering (map_lp_iterm d id (lp_ieval (captured!i) eta)) m) indices ms"
    "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d child eta)"
    "lpc_seg_projection_context filtering (\<lambda>x. A (LPIFun (c u)
      (x#map (\<lambda>t. map_lp_iterm d id (lp_ieval t eta)) captured)))"
    "(A (lpc_seg_runtime_value is_cont c d l eta),
      A (LPIFun (c u) (lpc_seg_runtime_value is_cont c d child eta#
        map (\<lambda>t. map_lp_iterm d id (lp_ieval t eta)) captured)))\<in>lpc_seg_projected_rel filtering R"
proof -
  let ?caps="map (\<lambda>t. map_lp_iterm d id (lp_ieval t eta)) captured"
  let ?child="lpc_seg_runtime_value is_cont c d child eta"
  obtain indices where af: "afs filtering (c u,Suc (length captured))=AFList (0#map Suc indices)"
    by (rule lpc_seg_projected_continuation_filterD[OF filter]) blast
  have two: "(2::nat)=Suc 1" by simp
  have shape: "lpc_seg_role_value 2 is_cont c d (lp_ieval (Fun u (child#captured)) eta) = LPIFun (c u) (?child#?caps)"
    by (simp only: two lp_ieval.simps list.map
      lpc_seg_role_continuation[where is_cont=is_cont and u=u and n=1 and c=c and d=d, OF cont]
      lpc_seg_runtime_value_def map_map o_def)
  have edge: "(lpc_seg_runtime_value is_cont c d l eta,LPIFun (c u) (?child#?caps))\<in>lpc_seg_projected_rel filtering R"
    using lpc_seg_projected_emit_edge[OF checked observed[unfolded lpc_seg_runtime_value_def]]
    by (simp only: shape lpc_seg_runtime_value_def)
  have target: "lpc_seg_has_projection filtering (LPIFun (c u) (?child#?caps))"
    using edge by (auto simp: lpc_seg_projected_rel_def lpc_seg_has_projection_def)
  have af': "afs filtering (c u,Suc (length ?caps))=AFList (0#map Suc indices)" using af by simp
  obtain n :: "('g,string) term" and ms :: "('g,string) term list" where pr: "lp_iproject filtering ?child n"
    and caps: "list_all2 (\<lambda>i m. i<length ?caps \<and> lp_iproject filtering (?caps!i) m) indices ms"
    by (rule lpc_seg_projected_pending_components[OF af' target]) blast
  have cap_terms: "list_all2 (\<lambda>i m. i<length captured \<and>
    lp_iproject filtering (map_lp_iterm d id (lp_ieval (captured!i) eta)) m) indices ms"
    using caps by (auto simp: list_all2_conv_all_nth)
  have child_pr: "lpc_seg_has_projection filtering ?child" using pr by (auto simp: lpc_seg_has_projection_def)
  have ctxt: "lpc_seg_projection_context filtering (\<lambda>x. A (LPIFun (c u) (x#?caps)))"
    by (rule lpc_seg_projection_context.frame[OF ambient af' caps])
  show thesis by (rule that[OF af cap_terms child_pr ctxt lpc_seg_projection_context_step[OF ambient edge]])
qed

end
