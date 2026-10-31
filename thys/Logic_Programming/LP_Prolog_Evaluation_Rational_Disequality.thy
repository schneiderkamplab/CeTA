theory LP_Prolog_Evaluation_Rational_Disequality
  imports LP_Prolog_Evaluation_Ground_Disequality
begin

definition lpp_check_evaluation_rational_disequality where
  "lpp_check_evaluation_rational_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser lpp_disequality_predicate) [a,b])#gs),active)#saved \<and>
     list_all (\<lambda>holds. lpp_check_evaluation_link T (if holds then yes_facts else no_facts)
       fuel Q nds states contexts Fs nd (if holds then (LPCGoals gs,active)#saved else saved)
       (lpcn_ground nd) (lpcn_guards nd @ (if holds then [LPCEqGuard a b False] else []))
       [] F source_context (if holds then yes else no)) [False,True])"

lemma lpp_rational_disequality_step:
  fixes a b :: "(string lp_cut_symbol,string) lp_iterm"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser lpp_disequality_predicate) [a,b])#gs),eta)#saved) event tt
    \<longleftrightarrow> event=None \<and> tt=(if \<exists>sigma :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm. lp_isubst a sigma=lp_isubst b sigma
      then saved else (LPCGoals gs,eta)#saved)"
proof (cases "\<exists>sigma :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm. lp_isubst a sigma=lp_isubst b sigma")
  case True
  have selected: "(lpp_disequality_predicate,length [a,b])\<in>lpp_builtin_signature"
    using lpp_disequality_names(6) by (simp add: numeral_2_eq_2)
  have outcomes: "\<And>outcome. lpp_finite_source_builtin lpp_disequality_predicate [a,b] outcome \<longleftrightarrow> outcome=LPPBuiltinFailure"
    by (simp add: lpp_finite_source_builtin_def lpp_rational_disequality_outcome_def True)
  show ?thesis using lpp_builtin_failure_only[where U=lpp_finite_source_builtin and P=P and gs=gs and eta=eta and es=saved,
      OF selected outcomes] True by simp
next
  case False
  have selected: "(lpp_disequality_predicate,length [a,b])\<in>lpp_builtin_signature"
    using lpp_disequality_names(6) by (simp add: numeral_2_eq_2)
  have outcomes: "\<And>outcome. lpp_finite_source_builtin lpp_disequality_predicate [a,b] outcome \<longleftrightarrow> outcome=LPPBuiltinSuccess LPIVar"
    by (simp add: lpp_finite_source_builtin_def lpp_rational_disequality_outcome_def False)
  show ?thesis using lpp_builtin_success_only[where U=lpp_finite_source_builtin and P=P and gs=gs and eta=eta and es=saved,
      OF selected outcomes] False by simp
qed

theorem lpp_evaluation_rational_disequality_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_rational_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?holds = "\<not>(\<exists>sigma :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm. lp_isubst (lp_ieval a eta) sigma=lp_isubst (lp_ieval b eta) sigma)"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  let ?guards = "lpcn_guards nd @ (if ?holds then [LPCEqGuard a b False] else [])"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser lpp_disequality_predicate) [a,b])#gs),active)#saved"
    using checked by (simp add: lpp_check_evaluation_rational_disequality_def)
  have link: "lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts)
    fuel Q nds states contexts Fs nd ?next (lpcn_ground nd) ?guards [] F source_context
    (if ?holds then yes else no)"
    using checked by (auto simp: lpp_check_evaluation_rational_disequality_def list_all_iff)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_rational_disequality_step split: if_splits)
  have extended: "lp_cut_knowledge (set (lpcn_ground nd)) ?guards eta"
    using known by (auto simp: lp_cut_knowledge_def split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis using lpp_evaluation_link_sound[OF contract evaluation program link equations refl extended free observed] actual by auto
qed

lemma lpp_evaluation_rational_disequality_domain:
  assumes checked: "lpp_check_evaluation_rational_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
  using checked by (simp add: lpp_check_evaluation_rational_disequality_def lpc_return_eval_def lpp_finite_source_domain_def)

ML \<open>
val checked = [@{thm lpp_evaluation_rational_disequality_sound}, @{thm lpp_evaluation_rational_disequality_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted rational disequality dependency" else ();
\<close>
end
