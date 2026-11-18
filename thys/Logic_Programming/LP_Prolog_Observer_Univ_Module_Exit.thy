theory LP_Prolog_Observer_Univ_Module_Exit
 imports LP_Prolog_Observer_Univ_Exit_Check
begin

lemma lpp_checked_univ_module_exit:
 assumes program: "lp_cut_source_program P"
 and coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpp_check_observer_univ_exit (Fs!i) (states!i)"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions xs t"
 and frame: "lpp_observer_univ_frame xs"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain xs event result"
 shows "\<not>lpp_observer_internal_frame result"
proof -
 obtain swaps i eta where bound: "i<length nds"
 and shape: "lpc_return_scope_word swaps xs=lpc_return_eval eta (states!i)"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
  using represented by (auto simp: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)
 have canonical_frame: "lpp_observer_univ_frame (lpc_return_eval eta (states!i))"
  using frame shape by (metis lpp_observer_univ_frame_scopes)
 have check: "lpp_check_observer_univ_exit (Fs!i) (states!i)"
  by (rule coverage[OF bound canonical_frame])
 have scoped: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta (states!i)) event (lpc_return_scope_word swaps result)"
  using lpp_observer_domain_scope_step[OF program step, of swaps] by (simp only: shape)
 have "\<not>lpp_observer_internal_frame (lpc_return_scope_word swaps result)"
  by (rule lpp_checked_observer_univ_exit[OF check free scoped])
 then show ?thesis by (simp add: lpp_observer_internal_scopes)
qed

ML \<open>
val checked = @{thms lpp_checked_univ_module_exit};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted module univ exits" else ();
\<close>
end
