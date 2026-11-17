theory LP_Prolog_Univ_Arithmetic_Normalization
 imports LP_Prolog_Univ_Source LP_Prolog_Stable_Normalization
begin

lemma lpp_univ_is_uses_shared_equality:
 assumes step: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
 shows "event=None \<and> (tt=[] \<or> (\<exists>f.
    lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<and>
    lpc_answer_transition P
      ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt))"
proof -
 have selected: "(''2:is'',length [a,e])\<in>lpp_builtin_signature"
  by (simp add: lpp_builtin_signature_def)
 have same: "\<And>outcome. lpp_univ_source_builtin names operation ''2:is'' [a,e] outcome =
   lpp_stable_source_builtin operation ''2:is'' [a,e] outcome"
  by (simp add: lpp_univ_source_builtin_def)
 have old: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  using step by (simp only: lpp_selected_builtin_cong[where U="lpp_univ_source_builtin names operation" and V="lpp_stable_source_builtin operation", OF selected same])
 show ?thesis by (rule lpp_stable_is_uses_shared_equality[OF old])
qed

lemma lpp_univ_evaluation_domain_contract:
  fixes P :: "(string,string) lp_cut_program"
    and a e :: "(string lp_cut_symbol,string) lp_iterm"
    and eta :: "'v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    and ret :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) \<Rightarrow> 'r"
    and R :: "'r rel" and t :: "'r"
  assumes domain: "lpp_finite_source_domain ''2:is'' [a,e]"
    and contracts: "\<And>f. lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<Longrightarrow>
      lp_answer_contract
        (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
        ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) R t ret"
  shows "lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) R t ret"
proof (rule lp_answer_contract_intro)
  let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
  fix event tt
  assume step: "?T ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
    using step domain by (auto simp: lpp_domain_answers_def lpp_univ_source_domain_def)
  have no_answer: "event=None" and cover: "tt=[] \<or> (\<exists>f.
    lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<and>
    lpc_answer_transition P
      ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt)"
    using lpp_univ_is_uses_shared_equality[OF actual] by auto
  have child: "lp_answer_contract ?T tt R t ret"
  proof (cases "tt=[]")
    case True
    have empty: "lp_answer_contract ?T [] R t ret"
    proof (rule lp_answer_contract_intro)
      fix ev :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and us
      assume "?T [] ev us"
      then have "([],map fst us)\<in>lpp_atomic_source P lpp_builtin_signature (lpp_univ_source_builtin names operation)"
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
val checked = [@{thm lpp_univ_is_uses_shared_equality}, @{thm lpp_univ_evaluation_domain_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ arithmetic normalization dependency" else ();
\<close>
end
