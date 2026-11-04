theory LP_Prolog_Equation_Rewrite
 imports LP_Prolog_Evaluation_Representation LP_Rational_Graph_Equations LP_Prolog_Equation_Congruence
begin

text \<open>A representation-only unfolding uses an initialized equation in
this state's context. The saved alternatives and return environment are kept
identical. The existing checked link still supplies a strict residual edge.\<close>

definition lpp_check_equation_rewrite where
  "lpp_check_equation_rewrite context a b =
    lpp_check_context_equation_rewrite context a b"

lemma lpp_equation_rewrite_equal:
  assumes "lpp_check_equation_rewrite context a b"
    "lpp_evaluation_context_holds E SP context eta"
  shows "lp_ieval a eta=lp_ieval b eta"
  by (rule lpp_context_equation_rewrite_sound[OF _ assms(2)])
    (use assms(1) in \<open>simp add: lpp_check_equation_rewrite_def\<close>)

lemma lpp_equation_rewrite_frame:
  assumes "lpp_check_equation_rewrite context a b"
    "lpp_evaluation_context_holds E SP context eta"
  shows "lpc_return_eval eta ((LPCGoals (LPCAtom a#gs),active)#saved) =
    lpc_return_eval eta ((LPCGoals (LPCAtom b#gs),active)#saved)"
  using lpp_equation_rewrite_equal[OF assms]
  by (simp add: lpc_return_eval_def)

lemma lpp_equation_rewrite_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and rewrite: "lpp_check_equation_rewrite source_context a b"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCGoals (LPCAtom b#gs),active)#saved) (lpcn_ground nd) (lpcn_guards nd)
      [] F source_context e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs
      (lpc_return_scope_word swaps (lpc_return_eval eta ((LPCGoals (LPCAtom a#gs),active)#saved))) u"
proof -
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have same: "lpc_return_eval eta ((LPCGoals (LPCAtom a#gs),active)#saved) =
    lpc_return_eval eta ((LPCGoals (LPCAtom b#gs),active)#saved)"
    by (rule lpp_equation_rewrite_frame[OF rewrite observed])
  show ?thesis using lpp_evaluation_link_sound[OF contract evaluation program
      checked equations refl known free observed] by (simp only: same)
qed

lemma lpp_clause_equation_rewrite_frame:
  assumes "lpp_check_equation_rewrite context a b"
    "lpp_evaluation_context_holds E SP context eta"
  shows "lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved) =
    lpc_return_eval eta ((LPCClause (LPCAtom b#gs) c m,active)#saved)"
  using lpp_equation_rewrite_equal[OF assms]
  by (simp add: lpc_return_eval_def)

lemma lpp_clause_equation_rewrite_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and rewrite: "lpp_check_equation_rewrite source_context a b"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCClause (LPCAtom b#gs) c m,active)#saved) (lpcn_ground nd) (lpcn_guards nd)
      [] F source_context e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs
      (lpc_return_scope_word swaps (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved))) u"
proof -
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have same: "lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved) =
    lpc_return_eval eta ((LPCClause (LPCAtom b#gs) c m,active)#saved)"
    by (rule lpp_clause_equation_rewrite_frame[OF rewrite observed])
  show ?thesis using lpp_evaluation_link_sound[OF contract evaluation program
      checked equations refl known free observed] by (simp only: same)
qed

lemma lpp_equation_rewrite_missing_context:
  "a\<noteq>b \<Longrightarrow> \<not>lpp_check_equation_rewrite (facts,guards,[]) a b"
  by (simp add: lpp_check_equation_rewrite_def lpp_check_context_equation_rewrite_def)

end
