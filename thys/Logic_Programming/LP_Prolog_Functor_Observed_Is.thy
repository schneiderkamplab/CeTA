theory LP_Prolog_Functor_Observed_Is
 imports LP_Prolog_Stable_Functor_Link LP_Prolog_Univ_Initialization LP_Prolog_Univ_Arithmetic_Normalization
begin

definition lpp_check_observed_functor_link where
  "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts nd F ss source_context source_functors a e gs active saved result_var middle =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     lpp_fresh_return result_var ss \<and> lpp_context_fresh result_var source_context \<and>
     list_all (lpp_functor_fact_fresh result_var) source_functors \<and>
     result_var\<notin>set F \<and> result_var\<notin>set (lpcn_vars nd) \<and> list_all (lpp_fresh_guard result_var) (lpcn_guards nd) \<and>
     lpcl_swaps middle=[] \<and>
     lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd
       ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
       (result_var#lpcn_ground nd) (lpcn_guards nd) [] F
       (lpp_add_evaluation_observation e (Var result_var) source_context) source_functors middle)"

theorem lpp_functor_observed_is_domain_context:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts nd F ss source_context source_functors a e gs active saved result_var middle"
    and domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and invariant: "J (lpc_return_eval eta ss)"
    and normalized: "\<And>f. J (lpc_return_eval eta ss) \<Longrightarrow>
      J ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
        lpc_return_env active eta)#lpc_return_eval eta saved)"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<Longrightarrow>
      J (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      C (lpc_return_eval rho (states!lpcl_target middle))"
  shows "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta] \<and> (\<forall>f.
    lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) []) \<longrightarrow>
    C ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved))"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and result_var: "lpp_fresh_return result_var ss"
    and context_fresh: "lpp_context_fresh result_var source_context"
    and functor_fresh: "list_all (lpp_functor_fact_fresh result_var) source_functors"
    and free_fresh: "result_var\<notin>set F"
    and interface: "result_var\<notin>set (lpcn_vars nd)"
    and guards: "list_all (lpp_fresh_guard result_var) (lpcn_guards nd)"
    and swaps: "lpcl_swaps middle=[]"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd
      ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
      (result_var#lpcn_ground nd) (lpcn_guards nd) [] F
      (lpp_add_evaluation_observation e (Var result_var) source_context) source_functors middle"
    using checked by (auto simp: lpp_check_observed_functor_link_def)
  have contracts: "C
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    if evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
  proof -
  let ?nu = "eta(result_var:=(LPIFun (LPCUser f) []))"
  let ?synthetic = "((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)"
  have fa: "result_var\<notin>vars_term a" and fe: "result_var\<notin>vars_term e"
    and rest: "lpp_fresh_return result_var ((LPCGoals gs,active)#saved)"
    using result_var by (auto simp: shape lpp_fresh_return_def)
  have unchanged: "lpc_return_eval ?nu ((LPCGoals gs,active)#saved)=lpc_return_eval eta ((LPCGoals gs,active)#saved)"
    by (rule lpp_fresh_return_eval[OF rest])
  have represented: "lpc_return_eval ?nu ?synthetic =
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    using unchanged lpp_fresh_term_eval[OF fa, of eta "LPIFun (LPCUser f) []"]
    by (simp add: lpc_return_eval_def)
  have extended: "lp_cut_knowledge (set (result_var#lpcn_ground nd)) (lpcn_guards nd) ?nu"
    using known guards lpp_fresh_guard_eval[of result_var _ eta "LPIFun (LPCUser f) []"]
      by (auto simp: lp_cut_knowledge_def list_all_iff intro: lp_seg_ground.intros)
  have parent: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)"
    using interface by (auto intro!: map_cong)
  have old_context: "lpp_stable_context_holds operation SP source_context ?nu"
    using lpp_stable_context_fresh_eval[OF context_fresh, of operation SP eta "LPIFun (LPCUser f) []"] observed by simp
  have evaluation: "lpp_stable_scalar_evaluation operation (lp_ieval e ?nu) (lp_ieval (Var result_var) ?nu)"
    using evaluated by (simp add: lpp_fresh_term_eval[OF fe])
  have facts: "lpp_stable_context_holds operation SP (lpp_add_evaluation_observation e (Var result_var) source_context) ?nu"
    by (rule lpp_stable_add_evaluation_context[OF old_context evaluation])
  have extended_free: "lpc_free_knowledge (set F) ?nu"
    using free free_fresh by (auto simp: lpc_free_knowledge_def inj_on_def)
  have extended_functors: "list_all (lpp_functor_fact_holds names ?nu) source_functors"
    using functors functor_fresh by (auto simp: list_all_iff lpp_functor_fact_fresh_eval)
  have equations: "lp_equations [] ?nu" by (simp add: lp_equations_def)
  obtain rho where same: "lpc_return_eval ?nu ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
    and child_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
    and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_stable_functor_link_witness[OF compatible program link equations parent extended extended_free facts extended_functors] by (simp add: swaps) blast
  have child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
    using normalized[OF invariant, of f] represented same by simp
  have child: "C
    (lpc_return_eval rho (states!lpcl_target middle))"
    by (rule lower[OF r_into_trancl[OF edge] knowledge child_free child_context child_functors child_invariant])
  show "C
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    using child same represented by simp
  qed
  show ?thesis using domain contracts by blast
qed

lemma lpp_observed_functor_result_capture_rejected:
 "observation\<in>set source_functors \<Longrightarrow> \<not> lpp_functor_fact_fresh result_var observation \<Longrightarrow>
  \<not> lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts nd F ss
    source_context source_functors a e gs active saved result_var middle"
 by (auto simp: lpp_check_observed_functor_link_def list_all_iff)

lemma lpp_observed_functor_missing_table_rejected:
 "\<not> lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs [] nd F ss
    source_context source_functors a e gs active saved result_var middle"
 by (simp add: lpp_check_observed_functor_link_def lpp_check_evaluation_functor_link_def)

theorem lpp_functor_observed_is_domain_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts nd F ss source_context source_functors a e gs active saved result_var middle"
    and domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and invariant: "J (lpc_return_eval eta ss)"
    and normalized: "\<And>f. J (lpc_return_eval eta ss) \<Longrightarrow>
      J ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
        lpc_return_env active eta)#lpc_return_eval eta saved)"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<Longrightarrow>
      J (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_return_eval eta ss) R t ret"
proof -
  have facts: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta] \<and> (\<forall>f.
    lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) []) \<longrightarrow>
    (\<lambda>xs. lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain) xs R t ret) ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved))"
    by (rule lpp_functor_observed_is_domain_context[where C="(\<lambda>xs. lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain) xs R t ret)" and J=J,
      OF compatible program checked domain known free observed functors invariant]) (fact normalized, fact lower)
  have ground: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]" using facts by blast
  have contracts: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    if "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
    using facts that by blast
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    using checked by (auto simp: lpp_check_observed_functor_link_def)
  show ?thesis using lpp_univ_evaluation_domain_contract[OF ground contracts]
    by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = [@{thm lpp_functor_observed_is_domain_context}, @{thm lpp_functor_observed_is_domain_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor observed arithmetic dependency" else ();
\<close>
end
