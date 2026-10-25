theory LP_Cut_Free_Refutation
  imports LP_Cut_Mixed_Free_Coverage LP_Cut_Inconsistent
begin

definition lpc_check_free_refutation where
  "lpc_check_free_refutation fuel G F guards i k =
    (i<length guards \<and> (case guards!i of LPCHeadGuard a h False \<Rightarrow>
      lpc_check_mixed_free_call fuel k G F a h | _ \<Rightarrow> False))"

lemma lpc_check_free_refutation_sound:
  assumes checked: "lpc_check_free_refutation fuel G F guards i k"
    and known: "lp_cut_knowledge (set G) guards eta"
    and free: "lpc_free_knowledge (set F) eta"
  shows False
proof -
  obtain a h where i: "i<length guards" and shape: "guards!i=LPCHeadGuard a h False"
    and mixed: "lpc_check_mixed_free_call fuel k G F a h"
    using checked by (auto simp: lpc_check_free_refutation_def split: lp_cut_guard.splits bool.splits)
  have holds: "lp_cut_guard_holds (guards!i) eta"
    using known i by (auto simp: lp_cut_knowledge_def list_all_iff)
  have ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)" using known by (simp add: lp_cut_knowledge_def)
  show False using lpc_check_mixed_free_call_sound[OF mixed ground free] holds
    by (simp add: shape)
qed

end
