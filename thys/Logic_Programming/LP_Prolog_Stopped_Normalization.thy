theory LP_Prolog_Stopped_Normalization
  imports LP_Prolog_Stopped_Primitive LP_Prolog_Stable_Normalization
begin

lemma lpp_stopped_evaluation_normalized_contract:
  fixes P :: "(string,string) lp_cut_program"
    and a e :: "(string lp_cut_symbol,string) lp_iterm"
    and eta :: "'v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    and ret :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) \<Rightarrow> 'r"
    and R :: "'r rel" and t :: "'r"
  assumes ground: "lp_seg_ground e"
    and contracts: "\<And>f. lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<Longrightarrow>
      lp_answer_contract
        (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
        ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) R t ret"
  shows "lp_answer_contract
    (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) R t ret"
proof (rule lp_answer_contract_intro)
  let ?T = "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)"
  fix event tt
  assume step: "?T ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
    using step ground by (auto simp: lp_answer_stop_def lpp_undefined_answer_stop_def
      lpp_builtin_active_def lpp_builtin_signature_def lpp_domain_answers_def lpp_finite_source_domain_def)
  have no_answer: "event=None" and cover: "tt=[] \<or> (\<exists>f.
    lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<and>
    lpc_answer_transition P
      ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt)"
    using lpp_stable_is_uses_shared_equality[OF actual] by auto
  have child: "lp_answer_contract ?T tt R t ret"
  proof (cases "tt=[]")
    case True
    have empty: "lp_answer_contract ?T [] R t ret"
      by (rule lp_answer_contract_intro) simp
    show ?thesis using empty True by simp
  next
    case False
    obtain f where result_value: "lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) [])"
      and equality: "lpc_answer_transition P
        ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt"
      using cover False by blast
    have normalized: "?T ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt"
      unfolding lp_answer_stop_def lpp_undefined_answer_stop_def lpp_undefined_def
        lpp_builtin_active_def
      by (simp add: lpp_domain_answers_def; intro disjI1 lpp_answer_transition.base[OF _ equality])
        (simp add: lpp_builtin_active_def)
    show ?thesis by (rule lp_answer_contract_child[OF contracts[OF result_value] normalized])
  qed
  show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T tt R t ret"
    using child no_answer by simp
qed

ML \<open>
val checked = [@{thm lpp_stopped_evaluation_normalized_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped evaluation contract dependency" else ();
\<close>
end
