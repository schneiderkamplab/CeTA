theory LP_Cut_Domain_Return_Scope_Contracts
  imports LP_Cut_Domain_Return_Modular
begin

context cut_runtime_domain
begin

lemma precise_answer_path_scope_word:
  assumes program: "lp_cut_source_program P"
    and path: "(ss,tt)\<in>(precise_answer_steps P)\<^sup>*"
  shows "(lpc_return_scope_word swaps ss,lpc_return_scope_word swaps tt)\<in>(precise_answer_steps P)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step tt uu)
  obtain event where event: "precise_answer_transition P tt event uu"
    using step by (auto simp: precise_answer_steps_def)
  have edge: "(lpc_return_scope_word swaps tt,lpc_return_scope_word swaps uu)\<in>precise_answer_steps P"
    using precise_answer_transition_scope_word[OF event program, of swaps]
    by (auto simp: precise_answer_steps_def)
  show ?case using step edge by (blast intro: rtrancl_into_rtrancl)
qed

theorem precise_return_contract_scopes:
  assumes program: "lp_cut_source_program P"
    and contract: "precise_return_contract P ss R t ret"
  shows "precise_return_contract P (lpc_return_scope_word swaps ss) R t ret"
proof (unfold precise_return_contract_def, intro conjI allI impI)
  have sn: "SN_on (precise_source P) {map fst ss}"
    using contract by (simp add: precise_return_contract_def)
  show "SN_on (precise_source P) {map fst (lpc_return_scope_word swaps ss)}"
    using precise_scope_word_SN[OF program sn, of swaps]
    by (simp add: lpc_return_scope_word_erases)
next
  fix us tail rho
  assume path: "(lpc_return_scope_word swaps ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some rho) tail"
  have reached: "(ss,lpc_return_scope_word (rev swaps) us)\<in>(precise_answer_steps P)\<^sup>*"
    using precise_answer_path_scope_word[OF program path, of "rev swaps"]
    by (simp add: lpc_return_scope_word_inverse)
  have returned: "precise_answer_transition P (lpc_return_scope_word (rev swaps) us) (Some rho)
    (lpc_return_scope_word (rev swaps) tail)"
    by (rule precise_answer_transition_scope_word[OF event program])
  show "(t,ret rho)\<in>R\<^sup>*" using contract reached returned
    unfolding precise_return_contract_def by blast
qed


end
end
