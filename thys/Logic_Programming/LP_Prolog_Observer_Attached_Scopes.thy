theory LP_Prolog_Observer_Attached_Scopes
 imports LP_Prolog_Observer_Table_Contract
begin

text \<open>Graph scope transport must also respect the suspended continuation.
These rules require that the selected renamings fix that continuation; they do
not silently rename only the helper or erase caller cut scopes.\<close>

lemma lpp_observer_attach_scope:
 assumes fixed: "map (lp_cut_scope_goal rename) rest=rest"
 shows "lpc_return_scope rename (lpc_attach_answers rest ss)=
   lpc_attach_answers rest (lpc_return_scope rename ss)"
proof -
 have maps: "map (lp_cut_scope_goal rename) rest=map id rest" using fixed by simp
 have unchanged: "lp_cut_scope_goal rename g=g" if "g\<in>set rest" for g
  using maps that by (simp only: map_eq_conv id_apply; blast)
 have each: "lp_cut_scope_entry rename (lpc_attach_frame rest frame)=
   lpc_attach_frame rest (map_prod (lp_cut_scope_entry rename) id frame)" for frame
  by (cases frame; cases "fst frame")
   (auto simp: lp_cut_scope_goal_map unchanged)
 show ?thesis by (simp add: lpc_attach_answers_def map_map o_def map_prod_def split_def each)
qed

lemma lpp_observer_attach_scope_word:
 assumes fixed: "\<And>a b. (a,b)\<in>set swaps \<Longrightarrow> map (lp_cut_scope_goal (lp_cut_scope_swap a b)) rest=rest"
 shows "lpc_return_scope_word swaps (lpc_attach_answers rest ss)=
   lpc_attach_answers rest (lpc_return_scope_word swaps ss)"
 using fixed
 by (induct swaps arbitrary: ss) (auto simp: lpp_observer_attach_scope split: prod.splits)

lemma lpp_observer_scoped_contract_restore:
 assumes program: "lp_cut_source_program P"
 and fixed: "\<And>a b. (a,b)\<in>set swaps \<Longrightarrow> map (lp_cut_scope_goal (lp_cut_scope_swap a b)) rest=rest"
 and canonical: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe (lpc_return_scope_word swaps runtime))) R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe runtime)) R subject returned"
proof -
 have scoped: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_return_scope_word swaps (lpc_attach_answers rest (lpc_reinterface observe runtime))) R subject returned"
  using canonical by (simp add: lpp_observer_attach_scope_word[OF fixed] lpp_observer_reinterface_scopes)
 have reversed: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_return_scope_word (rev swaps) (lpc_return_scope_word swaps
      (lpc_attach_answers rest (lpc_reinterface observe runtime)))) R subject returned"
  by (rule lpp_domain_contract_scopes[OF program scoped])
 show ?thesis using reversed by (simp add: lpc_return_scope_word_inverse)
qed

lemma lpp_observer_unfixed_caller_cut_counterexample:
 assumes distinct: "a\<noteq>b"
 shows "lpc_return_scope (lp_cut_scope_swap a b)
   (lpc_attach_answers [LPCCut a] [(LPCGoals [],env)]) \<noteq>
   lpc_attach_answers [LPCCut a]
    (lpc_return_scope (lp_cut_scope_swap a b) [(LPCGoals [],env)])"
 using distinct by (simp add: lpc_attach_answers_def lp_cut_scope_swap_def)

ML \<open>
val checked = @{thms lpp_observer_attach_scope lpp_observer_attach_scope_word lpp_observer_scoped_contract_restore lpp_observer_unfixed_caller_cut_counterexample};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer attachment scopes" else ();
\<close>
end
