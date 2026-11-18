theory LP_Prolog_Observer_Equality_Module
 imports LP_Prolog_Observer_Reflexive_Simulation LP_Prolog_Observer_Pair_Simulation
begin

lemma lpp_observer_equality_frame_scope:
 "lpp_observer_equality_frame (lpc_return_scope r ss)=lpp_observer_equality_frame ss"
 by (induction ss rule: lpp_observer_equality_frame.induct) auto

lemma lpp_observer_equality_frame_scopes:
 "lpp_observer_equality_frame (lpc_return_scope_word swaps ss)=lpp_observer_equality_frame ss"
 proof (induct swaps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons ab swaps)
 obtain a b where pair: "ab=(a,b)" by (cases ab) auto
 show ?case by (simp only: pair lpc_return_scope_word.simps Cons.hyps lpp_observer_equality_frame_scope)
qed

lemma lpp_observer_equality_module_step:
 fixes SP :: "string lpp_success_clause list"
 assumes program: "lp_cut_source_program P"
 and coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_equality_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    node_conditions lpp_finite_execution i"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions xs t"
 and finite: "lpp_finite_execution xs"
 and equality: "lpp_observer_equality_frame xs"
 and step: "lpc_answer_transition P xs ev ys"
 shows "ev=None \<and> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions ys u \<and> lpp_finite_execution ys)"
proof -
 obtain swaps i eta where bound: "i<length nds"
 and conditions: "node_conditions i eta"
 and shape: "lpc_return_scope_word swaps xs=lpc_return_eval eta (states!i)"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and subject: "t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
  using represented by (auto simp: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)
 have frame: "lpp_observer_equality_frame (lpc_return_eval eta (states!i))"
  using equality shape lpp_observer_equality_frame_scopes by metis
 have invariant: "lpp_finite_execution (lpc_return_eval eta (states!i))"
  using finite shape by (metis lpp_finite_execution_scope_word)
 have scoped: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev (lpc_return_scope_word swaps ys)"
  using lpc_answer_transition_scope_word[OF step program, of swaps] by (simp only: shape)
 have node: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    node_conditions lpp_finite_execution i"
  by (rule coverage[OF bound frame])
 obtain u more where silent: "ev=None" and edge: "(t,u)\<in>(lp_ild Q)\<^sup>+"
 and child: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_return_scope_word more (lpc_return_scope_word swaps ys)) u"
 and preserved: "lpp_finite_execution (lpc_return_scope_word swaps ys)"
  using node[unfolded lpp_observer_node_simulation_def, rule_format, OF conditions known free observed functors invariant scoped]
  unfolding subject lpp_premised_functor_module_rep_def by blast
 have rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions ys u"
  unfolding lpp_premised_functor_module_rep_def
  by (rule exI[of _ "swaps@more"]) (simp add: lpc_return_scope_word_append child)
 show ?thesis using silent edge rep preserved by (simp add: lpp_finite_execution_scope_word) blast
qed

ML \<open>
val checked = @{thms lpp_observer_equality_frame_scope lpp_observer_equality_frame_scopes
 lpp_observer_equality_module_step lpp_reflexive_separation_node_simulation lpp_separated_pair_node_simulation};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted equality module simulation" else ();
\<close>
end
