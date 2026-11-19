theory LP_Cut_Domain_Free_Refutation
 imports LP_Cut_Domain_Return_Free_Check
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_check_free_refutation_sound:
  assumes checked: "lpc_check_free_refutation fuel G F guards i k"
    and known: "knowledge (set G) guards eta"
    and free: "lpc_free_knowledge (set F) eta"
  shows False
proof -
  obtain a h where i: "i<length guards" and shape: "guards!i=LPCHeadGuard a h False"
    and mixed: "lpc_check_mixed_free_call fuel k G F a h"
    using checked by (auto simp: lpc_check_free_refutation_def split: lp_cut_guard.splits bool.splits)
  have holds: "guard_holds (guards!i) eta"
    using known i by (auto simp: knowledge_def list_all_iff)
  have ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)" using known by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
  show False using check_mixed_free_call_sound[OF mixed ground free knowledge_domain[OF known]] holds
    by (simp add: shape cut_domain_head_def)
qed


end
end
