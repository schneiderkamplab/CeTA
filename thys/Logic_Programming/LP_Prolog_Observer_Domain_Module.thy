theory LP_Prolog_Observer_Domain_Module
 imports LP_Prolog_Observer_Univ_Checked_Step LP_Prolog_Stopped_Scopes
begin

lemma lpp_observer_domain_scope_step:
 assumes program: "lp_cut_source_program P"
 and step: "lpp_domain_answers P B U D xs ev ys"
 shows "lpp_domain_answers P B U D (lpc_return_scope_word swaps xs) ev (lpc_return_scope_word swaps ys)"
 using step by (auto simp: lpp_domain_answers_def lpp_builtin_domain_bad_scopes
   intro: lpp_answer_transition_scope_word[OF _ program])

lemma lpp_observer_domain_module_step:
 fixes SP :: "string lpp_success_clause list"
 assumes program: "lp_cut_source_program P"
 and scopes: "\<And>swaps xs. eligible xs \<Longrightarrow> eligible (lpc_return_scope_word swaps xs)"
 and local: "\<And>i eta ev ys. i<length nds \<Longrightarrow>
   eligible (lpc_return_eval eta (states!i)) \<Longrightarrow>
   node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   lpp_finite_execution (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpp_domain_answers P B U D (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow>
   ev=None \<and> (ys=[] \<or> (\<exists>u.
    ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions ys u))"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions xs t"
 and finite: "lpp_finite_execution xs"
 and admitted: "eligible xs"
 and step: "lpp_domain_answers P B U D xs ev ys"
 shows "ev=None \<and> (ys=[] \<or> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions ys u))"
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
 have eligible: "eligible (lpc_return_eval eta (states!i))" using scopes[OF admitted, of swaps] shape by simp
 have invariant: "lpp_finite_execution (lpc_return_eval eta (states!i))"
  using finite shape by (metis lpp_finite_execution_scope_word)
 have scoped: "lpp_domain_answers P B U D (lpc_return_eval eta (states!i)) ev (lpc_return_scope_word swaps ys)"
  using lpp_observer_domain_scope_step[OF program step, of swaps] by (simp only: shape)
 have result: "ev=None \<and> (lpc_return_scope_word swaps ys=[] \<or> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_return_scope_word swaps ys) u))"
  using local[OF bound eligible conditions known free observed functors invariant scoped] by (simp only: subject)
 have empty: "ys=[]" if "lpc_return_scope_word swaps ys=[]"
  using arg_cong[OF that, of "lpc_return_scope_word (rev swaps)"]
  by (simp add: lpc_return_scope_word_inverse lpp_stopped_scope_nil)
 have child: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions ys u"
  if represented_child: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_return_scope_word swaps ys) u" for u
 proof -
  obtain more where rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_return_scope_word more (lpc_return_scope_word swaps ys)) u"
   using represented_child unfolding lpp_premised_functor_module_rep_def by blast
  show ?thesis unfolding lpp_premised_functor_module_rep_def
   by (rule exI[of _ "swaps@more"]) (simp add: lpc_return_scope_word_append rep)
 qed
 show ?thesis using result empty child by blast
qed

ML \<open>
val checked = @{thms lpp_observer_domain_scope_step lpp_observer_domain_module_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted domain module simulation" else ();
\<close>
end
