theory LP_Prolog_Separation_Empty_Actions
 imports LP_Prolog_Separation_Functor_Link
begin

text \<open>Empty successor separation conditions are discharged explicitly.
Ordinary ground, free, equation, functor and saved-frame contexts remain checked
by the existing link and source-action rules. No incoming context is reset.\<close>

lemma lpp_empty_separation_functor_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and empty: "separation_contexts!lpcl_target e=[]"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
 by (rule lpp_separation_functor_link_sound[where source_separation="[]", OF compatible program checked separation_bound _ _ equations old known free observed functors])
   (simp_all add: empty lpp_check_separation_transport_def)

theorem lpp_empty_separation_admin_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts nd F ss source_context source_functors returned arity event next e"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and empty: "separation_contexts!lpcl_target e=[]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) actual tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. actual=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof -
  have admin: "lpc_return_admin ss=Some (event,next)"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd next (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
    and emit: "case event of None\<Rightarrow>True | Some ts\<Rightarrow>lpc_check_return_emit Q nd returned arity ts"
    using checked by (auto simp: lpp_check_functor_admin_node_def)
  have evaluated: "lpc_return_admin (lpc_return_eval eta ss) =
    Some (map_option (\<lambda>ts. lpc_return_env ts eta) event,lpc_return_eval eta next)"
    by (simp add: lpc_return_eval_admin admin)
  have same: "actual=map_option (\<lambda>ts. lpc_return_env ts eta) event \<and> tt=lpc_return_eval eta next"
    by (rule lpc_return_admin_unique[OF evaluated step])
  have successor: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps tt) u"
    using lpp_empty_separation_functor_link_sound[OF compatible program link separation_bound empty _ refl known free observed functors] same
    by (simp add: lp_equations_def)
  have returns: "\<forall>rho. actual=Some rho \<longrightarrow>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
  proof (intro allI impI)
    fix rho assume actual: "actual=Some rho"
    obtain ts where event: "event=Some ts" and rho: "rho=lpc_return_env ts eta"
      using same actual by (cases event) auto
    have check: "lpc_check_return_emit Q nd returned arity ts" using emit event by simp
    show "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
      using lpc_return_emit_sound[OF check, of eta] rho by auto
  qed
  show ?thesis using successor returns by blast
qed

theorem lpp_empty_separation_case_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts nd F source_context source_functors m f ts gs active saved e"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and empty: "separation_contexts!lpcl_target e=[]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd (lpc_return_case P m f ts gs active saved)
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
    using checked by (auto simp: lpp_check_functor_case_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using lpc_return_case_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))) u"
    using lpp_empty_separation_functor_link_sound[OF compatible program link separation_bound empty _ refl known free observed functors] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

theorem lpp_empty_separation_meta_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_meta_node T fs fuel Q nds states contexts Fs functor_contexts nd F source_context source_functors m a gs active saved body e"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and empty: "separation_contexts!lpcl_target e=[]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_meta m a gs (map fst saved) body"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd
      ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
    using checked by (auto simp: lpp_check_functor_meta_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using lpc_return_meta_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps
      (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))) u"
    using lpp_empty_separation_functor_link_sound[OF compatible program link separation_bound empty _ refl known free observed functors] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

ML \<open>
val checked = @{thms lpp_empty_separation_functor_link_sound lpp_empty_separation_admin_node_sound
 lpp_empty_separation_case_node_sound lpp_empty_separation_meta_node_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted empty separation actions" else ();
\<close>
end
