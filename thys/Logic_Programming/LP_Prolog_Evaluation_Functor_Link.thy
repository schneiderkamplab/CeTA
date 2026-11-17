theory LP_Prolog_Evaluation_Functor_Link
 imports LP_Prolog_Evaluation_Link LP_Prolog_Functor_Context
begin

text \<open>Functor observations extend the existing parameterized evaluation
context. Both contexts are checked against the same child and instance valuation;
no integer restriction is added to the evaluation relation.\<close>

definition lpp_check_evaluation_functor_link where
 "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts
   nd ss G K eqs F source_context source_functors e =
  (lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F source_context e \<and>
   lpcl_target e<length functor_contexts \<and>
   lpp_check_functor_transport source_functors (functor_contexts!lpcl_target e)
    (lp_cut_instance_subst (lpcl_bindings e)))"

lemma lpp_evaluation_functor_link_witness:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_evaluation_context_holds E SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>nu. lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!lpcl_target e)) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu \<and>
    lpc_free_knowledge (set (Fs!lpcl_target e)) nu \<and>
    lpp_evaluation_context_holds E SP (contexts!lpcl_target e) nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q \<and>
    list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target e)"
proof -
 have base: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F source_context e"
  using checked by (simp add: lpp_check_evaluation_functor_link_def)
 have transported: "list_all (lpp_functor_fact_holds names
    (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'))
    (functor_contexts!lpcl_target e)"
  by (rule lpp_check_functor_transport_sound[OF _ functors])
   (use checked in \<open>simp add: lpp_check_evaluation_functor_link_def\<close>)
 show ?thesis
  by (rule lpp_evaluation_link_witness_with_observation[where J="\<lambda>nu. list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target e)", OF contract evaluation program
    base equations old known free observed transported])
qed

lemma lpp_evaluation_functor_missing_table_rejected:
 "\<not> lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs []
   nd ss G K eqs F source_context source_functors e"
 by (simp add: lpp_check_evaluation_functor_link_def)

lemma lpp_evaluation_functor_missing_fact_rejected:
 "functor_contexts!lpcl_target e=[observation] \<Longrightarrow>
  \<not> lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts
   nd ss G K eqs F source_context [] e"
 by (simp add: lpp_check_evaluation_functor_link_def lpp_check_functor_transport_def)

lemma lpp_evaluation_functor_changed_arguments_rejected:
 "functor_contexts!lpcl_target e=[LPPFunctorFact (Var ''V'') (Var ''N'') (Var ''B'')] \<Longrightarrow>
  lp_cut_instance_subst (lpcl_bindings e)=Var \<Longrightarrow>
  \<not> lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts
   nd ss G K eqs F source_context [LPPFunctorFact (Var ''V'') (Var ''N'') (Var ''A'')] e"
 by (simp add: lpp_check_evaluation_functor_link_def lpp_check_functor_transport_def)

lemma lpp_evaluation_functor_empty_extension:
 "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts
   nd ss G K eqs F source_context [] e =
  (lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F source_context e \<and>
   lpcl_target e<length functor_contexts \<and> functor_contexts!lpcl_target e=[])"
 by (auto simp: lpp_check_evaluation_functor_link_def lpp_check_functor_transport_def list_all_iff)

ML \<open>
val checked = [@{thm lpp_evaluation_functor_link_witness}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted evaluation functor link dependency" else ();
\<close>
end
