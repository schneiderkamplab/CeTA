theory LP_Cut_Domain_Precise_Instance
  imports LP_Cut_Domain_Precise_Source
begin

text \<open>Domain-specific soundness for the existing executable checks.\<close>

context cut_runtime_domain
begin

lemma precise_scope_word_SN:
  assumes program: "lp_cut_source_program P" and sn: "SN_on (precise_source P) {s}"
  shows "SN_on (precise_source P) {lp_cut_scope_word rs s}"
  using sn
proof (induct rs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons ab rs)
  obtain a b where ab: "ab=(a,b)" by (cases ab) auto
  have first: "SN_on (precise_source P) {map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s}"
    by (rule precise_scope_swap_preserves_SN[OF program Cons.prems])
  show ?case using Cons.hyps[OF first] by (simp add: ab)
qed

theorem precise_checked_instance_SN:
  assumes program: "lp_cut_source_program P"
    and checked: "lp_cut_check_instance s G guards t H guards' bindings swaps"
    and sn: "SN_on (precise_source P)
      {lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>)}"
  shows "SN_on (precise_source P) {lp_cut_state_eval s \<eta>}"
proof -
  have source: "s=lp_cut_scope_word swaps
      (lp_cut_state_map (\<lambda>u. u\<cdot>lp_cut_instance_subst bindings) t)"
    using checked by (auto simp: lp_cut_check_instance_def Let_def)
  have shape: "lp_cut_state_eval s \<eta> = lp_cut_scope_word swaps
      (lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>))"
    by (simp add: source lp_cut_scope_word_map[symmetric] lp_cut_state_eval_subst)
  show ?thesis using precise_scope_word_SN[OF program sn, of swaps] shape by simp
qed

end
end
