theory LP_Prolog_Stable_Normalization
 imports LP_Prolog_Stable_Comparison_Node
begin

lemma lpp_stable_is_uses_shared_equality:
  assumes step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  shows "event=None \<and> (tt=[] \<or> (\<exists>f.
    lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<and>
    lpc_answer_transition P
      ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt))"
proof -
  have selected: "(''2:is'',2)\<in>lpp_builtin_signature" by (simp add: lpp_builtin_signature_def)
  have no_probe: "\<And>aa keep. \<not>lpp_stable_is_outcome operation a e (LPPBuiltinProbe aa keep)"
    by (auto simp: lpp_stable_is_outcome_def lpp_integer_is_outcome_def split: if_splits option.splits)
  have no_call: "\<And>aa. \<not>lpp_stable_is_outcome operation a e (LPPBuiltinCall aa)"
    by (auto simp: lpp_stable_is_outcome_def lpp_integer_is_outcome_def split: if_splits option.splits)
  have no_branch: "\<And>cs ys ns. \<not>lpp_stable_is_outcome operation a e (LPPBuiltinBranch cs ys ns)"
    by (auto simp: lpp_stable_is_outcome_def lpp_integer_is_outcome_def split: if_splits option.splits)
  from step consider
    (success) mu where "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu)" "event=None"
      "tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs),\<lambda>x. lp_isubst (eta x) mu)#saved"
  | (failure) "lpp_stable_is_outcome operation a e LPPBuiltinFailure" "event=None" "tt=saved"
  | (error) "event=None" "tt=[]"
    by (cases rule: lpp_answer_transition.cases)
      (use selected in \<open>auto simp: lpp_builtin_active_def lpp_stable_source_is numeral_2_eq_2 no_probe no_call no_branch\<close>)
  then show ?thesis
  proof cases
    case (success mu)
    obtain f where result_value: "lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) [])"
      and chosen: "lpp_scalar_unifier a f=Some mu"
      using success(1) by (auto simp: lpp_stable_is_outcome_def split: option.splits)
    have equality: "lpc_answer_transition P
      ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt"
      unfolding success(2,3) by (rule lpc_answer_transition.unify[OF lpp_scalar_unifier_mgu[OF chosen]])
    show ?thesis using success(2) result_value equality by blast
  next
    case failure
    obtain f where result_value: "lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) [])"
      and failed: "lpp_scalar_unifier a f=None"
      using failure(1) by (auto simp: lpp_stable_is_outcome_def split: option.splits)
    have impossible: "\<not>(\<exists>sigma. lp_isubst a sigma=lp_isubst (LPIFun (LPCUser f) []) sigma)"
      using lpp_scalar_unifier_complete[of a f] failed by simp
    have equality: "lpc_answer_transition P
      ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt"
      unfolding failure(2,3) by (rule lpc_answer_transition.unify_fail[OF impossible])
    show ?thesis using failure(2) result_value equality by blast
  next
    case error then show ?thesis by simp
  qed
qed


lemma lpp_stable_evaluation_normalized_contract:
  fixes P :: "(string,string) lp_cut_program"
    and a e :: "(string lp_cut_symbol,string) lp_iterm"
    and eta :: "'v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    and ret :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) \<Rightarrow> 'r"
    and R :: "'r rel" and t :: "'r"
  assumes ground: "lp_seg_ground e"
    and contracts: "\<And>f. lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<Longrightarrow>
      lp_answer_contract
        (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
        ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) R t ret"
  shows "lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) R t ret"
proof (rule lp_answer_contract_intro)
  let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain"
  fix event tt
  assume step: "?T ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
    using step ground by (auto simp: lpp_domain_answers_def lpp_finite_source_domain_def)
  have no_answer: "event=None" and cover: "tt=[] \<or> (\<exists>f.
    lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<and>
    lpc_answer_transition P
      ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt)"
    using lpp_stable_is_uses_shared_equality[OF actual] by auto
  have child: "lp_answer_contract ?T tt R t ret"
  proof (cases "tt=[]")
    case True
    have empty: "lp_answer_contract ?T [] R t ret"
    proof (rule lp_answer_contract_intro)
      fix ev :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and us
      assume "?T [] ev us"
      then have "([],map fst us)\<in>lpp_atomic_source P lpp_builtin_signature (lpp_stable_source_builtin operation)"
        by (auto simp: lpp_domain_answers_def dest: lpp_answer_transition_erases)
      then show "(\<forall>rho. ev=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T us R t ret"
        by (simp add: lpp_atomic_source_empty)
    qed
    show ?thesis using empty True by simp
  next
    case False
    obtain f where result_value: "lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) [])"
      and equality: "lpc_answer_transition P
        ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt"
      using cover False by blast
    have normalized: "?T ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt"
      unfolding lpp_domain_answers_def by (intro disjI1 lpp_answer_transition.base[OF _ equality])
        (simp add: lpp_builtin_active_def)
    show ?thesis by (rule lp_answer_contract_child[OF contracts[OF result_value] normalized])
  qed
  show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T tt R t ret"
    using child no_answer by simp
qed

ML \<open>
val checked = [@{thm lpp_stable_is_uses_shared_equality}, @{thm lpp_stable_evaluation_normalized_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable normalization dependency" else ();
\<close>
end
