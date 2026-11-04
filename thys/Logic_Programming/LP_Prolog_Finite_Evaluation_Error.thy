theory LP_Prolog_Finite_Evaluation_Error
 imports LP_Prolog_Finite_Comparison_Error
begin

text \<open>Uncaught instantiation errors discharge the whole annotated stack.
No helper return or failure alternative is produced.\<close>

lemma lpp_finite_evaluation_error_step:
  assumes error: "lpp_finite_instantiation_error e"
    and step: "lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain
      ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  shows "event=None \<and> tt=[]"
proof -
  have selected: "(''2:is'',length [a,e])\<in>lpp_builtin_signature"
    by (simp add: lpp_builtin_signature_def)
  have domain: "lpp_finite_source_domain ''2:is'' [a,e]"
    using error by (simp add: lpp_finite_source_domain_def)
  have actual: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
    using step domain by (auto simp: lpp_domain_answers_def)
  have outcome: "\<And>out. lpp_finite_source_builtin ''2:is'' [a,e] out \<longleftrightarrow> out=LPPBuiltinError"
    by (simp add: lpp_finite_source_builtin_def lpp_finite_is_instantiation_error[OF error])
  show ?thesis using actual selected
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def outcome)
qed

definition lpp_check_finite_evaluation_error where
  "lpp_check_finite_evaluation_error nd F ss source_context a e gs active saved =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     lpp_check_finite_instantiation_error
       (set (lpcn_ground nd) \<union> lpp_source_context_ground source_context) (set F) e)"

lemma lpp_finite_evaluation_error_contract:
  assumes checked: "lpp_check_finite_evaluation_error nd F ss source_context a e gs active saved"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP source_context eta"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    (lpc_return_eval eta ss) R t ret"
proof -
  let ?T = "lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and check: "lpp_check_finite_instantiation_error
      (set (lpcn_ground nd) \<union> lpp_source_context_ground source_context) (set F) e"
    using checked by (auto simp: lpp_check_finite_evaluation_error_def)
  have error: "lpp_finite_instantiation_error (lp_ieval e eta)"
  proof (rule lpp_checked_finite_instantiation_error[OF check])
    fix x assume "x\<in>set (lpcn_ground nd) \<union> lpp_source_context_ground source_context"
    then show "lp_seg_ground (eta x)"
      using known lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground observed]
      by (auto simp: lp_cut_knowledge_def)
  next
    fix x assume "x\<in>set F"
    then show "\<exists>y. eta x=LPIVar y" using free by (auto simp: lpc_free_knowledge_def)
  qed
  have empty: "lp_answer_contract ?T [] R t ret"
  proof (rule lp_answer_contract_intro)
    fix ev :: "(nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and us
    assume step: "?T [] ev us"
    have "([],map fst us)\<in>lpp_atomic_source P lpp_builtin_signature lpp_finite_source_builtin"
      using step by (auto simp: lpp_domain_answers_def dest: lpp_answer_transition_erases)
    then show "(\<forall>rho. ev=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T us R t ret"
      by (simp add: lpp_atomic_source_empty)
  qed
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix ev us assume step: "?T (lpc_return_eval eta ss) ev us"
    have "ev=None \<and> us=[]"
      using lpp_finite_evaluation_error_step[OF error] step
      by (simp add: shape lpc_return_eval_def)
    then show "(\<forall>rho. ev=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T us R t ret"
      using empty by simp
  qed
qed

ML \<open>
val checked = [@{thm lpp_finite_evaluation_error_step}, @{thm lpp_finite_evaluation_error_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite evaluation error dependency" else ();
\<close>
end
