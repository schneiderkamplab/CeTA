theory LP_Prolog_Stable_Admin
 imports LP_Prolog_Stable_Equality LP_Prolog_Evaluation_Allocate
begin

theorem lpp_stable_admin_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_admin_node T fs fuel Q nds states contexts Fs nd F ss source_context returned arity event next e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) actual tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. actual=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof -
  have admin: "lpc_return_admin ss=Some (event,next)"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd next (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    and emit: "case event of None\<Rightarrow>True | Some ts\<Rightarrow>lpc_check_return_emit Q nd returned arity ts"
    using checked by (auto simp: lpp_check_evaluation_admin_node_def)
  have evaluated: "lpc_return_admin (lpc_return_eval eta ss) =
    Some (map_option (\<lambda>ts. lpc_return_env ts eta) event,lpc_return_eval eta next)"
    by (simp add: lpc_return_eval_admin admin)
  have same: "actual=map_option (\<lambda>ts. lpc_return_env ts eta) event \<and> tt=lpc_return_eval eta next"
    by (rule lpc_return_admin_unique[OF evaluated step])
  have successor: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u"
    using lpp_stable_link_sound[OF compatible program link _ refl known free observed] same
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

theorem lpp_stable_case_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_case_node T fs fuel P Q nds states contexts Fs nd F source_context m f ts gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd (lpc_return_case P m f ts gs active saved)
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked by (auto simp: lpp_check_evaluation_case_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using lpc_return_case_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))) u"
    using lpp_stable_link_sound[OF compatible program link _ refl known free observed] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

theorem lpp_stable_meta_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_meta_node T fs fuel Q nds states contexts Fs nd F source_context m a gs active saved body e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_meta m a gs (map fst saved) body"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked by (auto simp: lpp_check_evaluation_meta_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using lpc_return_meta_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps
      (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))) u"
    using lpp_stable_link_sound[OF compatible program link _ refl known free observed] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

ML \<open>
val checked = [@{thm lpp_stable_admin_node_sound}, @{thm lpp_stable_case_node_sound}, @{thm lpp_stable_meta_node_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable administrative dependency" else ();
\<close>
end
