theory LP_Prolog_Observer_Invariant
 imports LP_Prolog_Observer_Canonical_Node
begin

text \<open>The joint invariant covers the actual suspended caller in every
choice frame. Finite helper goals alone do not establish this invariant.\<close>

definition lpp_observer_invariant where
 "lpp_observer_invariant A specs rest runtime =
  (lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) \<and>
   lpp_leaf_stack_invariant A specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))"

lemma lpp_observer_invariant_scopes:
 assumes clear: "lpc_rest_scopes rest={}"
 shows "lpp_observer_invariant A specs rest (lpc_return_scope_word swaps runtime) =
   lpp_observer_invariant A specs rest runtime"
proof -
 have fixed: "map (lp_cut_scope_goal (lp_cut_scope_swap a b)) rest=rest" for a b
  by (rule lpp_observer_scope_free_rest_fixed[OF clear])
 show ?thesis unfolding lpp_observer_invariant_def
  by (simp add: lpp_observer_reinterface_scopes lpp_observer_attach_scope_word[OF fixed, symmetric]
    lpp_finite_execution_scope_word lpp_leaf_stack_scopes)
qed

lemma lpp_observer_invariant_substack:
 assumes contained: "set selected_rows \<subseteq> set runtime"
 and invariant: "lpp_observer_invariant A specs rest runtime"
 shows "lpp_observer_invariant A specs rest selected_rows"
 using contained invariant
 by (fastforce simp: lpp_observer_invariant_def lpp_finite_execution_def
   lpc_attach_answers_def lpc_reinterface_def lpp_leaf_stack_invariant_def list_all_iff)

lemma lpp_observer_invariant_missing_saved_finite:
 assumes bad: "\<not>lpp_finite_term (saved_env (Inr slot))"
 shows "\<not>lpp_observer_invariant A specs [LPCAtom (Var slot)]
   [(LPCGoals gs,active_env),(LPCGoals [],saved_env)]"
 using bad by (simp add: lpp_observer_invariant_def lpc_reinterface_def
   lpp_finite_execution_def lpc_attach_answers_def lpp_finite_goals_def)

ML \<open>
val checked = @{thms lpp_observer_invariant_scopes lpp_observer_invariant_substack
 lpp_observer_invariant_missing_saved_finite};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted joint observer invariant" else ();
\<close>
end
