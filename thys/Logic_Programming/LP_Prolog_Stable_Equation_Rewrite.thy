theory LP_Prolog_Stable_Equation_Rewrite
 imports LP_Prolog_Stable_Contract_Refinement LP_Prolog_Equation_Rewrite
begin

lemma lpp_stable_equation_rewrite_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and rewrite: "lpp_check_equation_rewrite source_context a b"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCGoals (LPCAtom b#gs),active)#saved) (lpcn_ground nd) (lpcn_guards nd)
      [] F source_context e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs
      (lpc_return_scope_word swaps (lpc_return_eval eta ((LPCGoals (LPCAtom a#gs),active)#saved))) u"
proof -
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have same: "lpc_return_eval eta ((LPCGoals (LPCAtom a#gs),active)#saved) =
    lpc_return_eval eta ((LPCGoals (LPCAtom b#gs),active)#saved)"
    by (rule lpp_equation_rewrite_frame[OF rewrite lpp_stable_context_finite_envelope[OF compatible observed]])
  show ?thesis using lpp_stable_link_sound[OF compatible program
      checked equations refl known free observed] by (simp only: same)
qed

lemma lpp_stable_clause_equation_rewrite_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and rewrite: "lpp_check_equation_rewrite source_context a b"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCClause (LPCAtom b#gs) c m,active)#saved) (lpcn_ground nd) (lpcn_guards nd)
      [] F source_context e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs
      (lpc_return_scope_word swaps (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved))) u"
proof -
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have same: "lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved) =
    lpc_return_eval eta ((LPCClause (LPCAtom b#gs) c m,active)#saved)"
    by (rule lpp_clause_equation_rewrite_frame[OF rewrite lpp_stable_context_finite_envelope[OF compatible observed]])
  show ?thesis using lpp_stable_link_sound[OF compatible program
      checked equations refl known free observed] by (simp only: same)
qed
ML \<open>
val checked = [@{thm lpp_stable_equation_rewrite_link_sound}, @{thm lpp_stable_clause_equation_rewrite_link_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable equation rewrite dependency" else ();
\<close>
end
