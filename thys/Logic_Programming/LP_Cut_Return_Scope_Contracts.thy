theory LP_Cut_Return_Scope_Contracts
  imports LP_Cut_Return_Allocate LP_Cut_Return_Modular
begin

lemma lpc_return_scope_word_erases:
  "map fst (lpc_return_scope_word swaps ss) = lp_cut_scope_word swaps (map fst ss)"
  by (induct swaps arbitrary: ss)
    (auto simp: lpc_return_scope_erases split: prod.splits)

lemma lpc_answer_path_scope_word:
  assumes program: "lp_cut_source_program P"
    and path: "(ss,tt)\<in>(lpc_answer_steps P)\<^sup>*"
  shows "(lpc_return_scope_word swaps ss,lpc_return_scope_word swaps tt)\<in>(lpc_answer_steps P)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step tt uu)
  obtain event where event: "lpc_answer_transition P tt event uu"
    using step by (auto simp: lpc_answer_steps_def)
  have edge: "(lpc_return_scope_word swaps tt,lpc_return_scope_word swaps uu)\<in>lpc_answer_steps P"
    using lpc_answer_transition_scope_word[OF event program, of swaps]
    by (auto simp: lpc_answer_steps_def)
  show ?case using step edge by (blast intro: rtrancl_into_rtrancl)
qed

theorem lpc_return_contract_scopes:
  assumes program: "lp_cut_source_program P"
    and contract: "lpc_return_contract P ss R t ret"
  shows "lpc_return_contract P (lpc_return_scope_word swaps ss) R t ret"
proof (unfold lpc_return_contract_def, intro conjI allI impI)
  have sn: "SN_on (lp_cut_mgu_source P) {map fst ss}"
    using contract by (simp add: lpc_return_contract_def)
  show "SN_on (lp_cut_mgu_source P) {map fst (lpc_return_scope_word swaps ss)}"
    using lpc_mgu_scope_word_SN[OF program sn, of swaps]
    by (simp add: lpc_return_scope_word_erases)
next
  fix us tail rho
  assume path: "(lpc_return_scope_word swaps ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some rho) tail"
  have reached: "(ss,lpc_return_scope_word (rev swaps) us)\<in>(lpc_answer_steps P)\<^sup>*"
    using lpc_answer_path_scope_word[OF program path, of "rev swaps"]
    by (simp add: lpc_return_scope_word_inverse)
  have returned: "lpc_answer_transition P (lpc_return_scope_word (rev swaps) us) (Some rho)
    (lpc_return_scope_word (rev swaps) tail)"
    by (rule lpc_answer_transition_scope_word[OF event program])
  show "(t,ret rho)\<in>R\<^sup>*" using contract reached returned
    unfolding lpc_return_contract_def by blast
qed

end
