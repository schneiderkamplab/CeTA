theory LP_Prolog_Functor_Admin
 imports LP_Prolog_Functor_Equality
begin

definition lpp_check_functor_admin_node where
  "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts nd F ss source_context source_functors returned arity event next e =
    (lpc_return_admin ss=Some (event,next) \<and>
     lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd next (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e \<and>
     (case event of None\<Rightarrow>True | Some ts\<Rightarrow>lpc_check_return_emit Q nd returned arity ts))"

theorem lpp_functor_admin_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts nd F ss source_context source_functors returned arity event next e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) actual tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_functor_rep names E SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u) \<and>
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
    lpp_functor_rep names E SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u"
    using lpp_evaluation_functor_link_sound[OF contract evaluation program link _ refl known free observed functors] same
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

lemma lpp_functor_admin_missing_table_rejected:
 "\<not> lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs [] nd F ss
   source_context source_functors returned arity event next e"
 by (simp add: lpp_check_functor_admin_node_def lpp_check_evaluation_functor_link_def)

ML \<open>
val checked = [@{thm lpp_functor_admin_node_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor administrative dependency" else ();
\<close>
end
