theory LP_Prolog_Univ_Normalization
 imports LP_Prolog_Univ_Decomposition LP_Prolog_Finite_Length_Normalization
begin

text \<open>Univ decomposition is normalized through the existing answer-machine
equality transition. Failure resumes exactly the saved alternatives; an uncaught
error discards them. The source profile must supply the stated outcome coverage.\<close>

lemma lpp_univ_uses_shared_equality:
 assumes selected: "(''2:=..'',2)\<in>B"
 and coverage: "\<And>out. U ''2:=..'' [LPIFun f ts,requested] out \<Longrightarrow>
   lpp_univ_decompose_outcome names (LPIFun f ts) requested out"
 and step: "lpp_answer_transition P B U
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,requested])#gs),eta)#saved) event tt"
 shows "event=None \<and> (tt=[] \<or>
   lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) event tt)"
proof -
 have no_probe: "\<And>aa keep. \<not>U ''2:=..'' [LPIFun f ts,requested] (LPPBuiltinProbe aa keep)"
  using coverage by (fastforce simp: lpp_univ_decompose_outcome_def)
 have no_call: "\<And>aa. \<not>U ''2:=..'' [LPIFun f ts,requested] (LPPBuiltinCall aa)"
  using coverage by (fastforce simp: lpp_univ_decompose_outcome_def)
 have no_branch: "\<And>cs ys ns. \<not>U ''2:=..'' [LPIFun f ts,requested] (LPPBuiltinBranch cs ys ns)"
  using coverage by (fastforce simp: lpp_univ_decompose_outcome_def)
 have no_choice: "\<And>left right. \<not>U ''2:=..'' [LPIFun f ts,requested] (LPPBuiltinChoice left right)"
  using coverage by (fastforce simp: lpp_univ_decompose_outcome_def)
 from step consider
   (success) mu where "U ''2:=..'' [LPIFun f ts,requested] (LPPBuiltinSuccess mu)" "event=None"
    "tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs),\<lambda>x. lp_isubst (eta x) mu)#saved"
 | (failure) "U ''2:=..'' [LPIFun f ts,requested] LPPBuiltinFailure" "event=None" "tt=saved"
 | (error) "event=None" "tt=[]"
  by (cases rule: lpp_answer_transition.cases)
   (use selected in \<open>auto simp: lpp_builtin_active_def numeral_2_eq_2 no_probe no_call no_branch no_choice\<close>)
 then show ?thesis
 proof cases
  case (success mu)
  have mgu: "lpc_mgu_unify requested (lpp_argument_list (LPIFun (names f) [] # ts)) gs mu"
   using coverage[OF success(1)] by (simp add: lpp_univ_decompose_outcome_def)
  have equality: "lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) event tt"
   unfolding success(2,3) by (rule lpc_answer_transition.unify[OF mgu])
  show ?thesis using equality success(2) by simp
 next
  case failure
  have impossible: "\<not>(\<exists>sigma :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm.
   lp_isubst requested sigma=lp_isubst (lpp_argument_list (LPIFun (names f) [] # ts)) sigma)"
   using coverage[OF failure(1)] by (simp add: lpp_univ_decompose_outcome_def)
  have equality: "lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) event tt"
   unfolding failure(2,3) by (rule lpc_answer_transition.unify_fail[OF impossible])
  show ?thesis using equality failure(2) by simp
 next
  case error then show ?thesis by simp
 qed
qed

lemma lpp_univ_normalized_contract:
 fixes P :: "(string,string) lp_cut_program"
 and eta :: "'v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and ret :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) \<Rightarrow> 'r"
 and R :: "'r rel" and t :: "'r"
 assumes selected: "(''2:=..'',2)\<in>B"
 and coverage: "\<And>out. U ''2:=..'' [LPIFun f ts,requested] out \<Longrightarrow>
   lpp_univ_decompose_outcome names (LPIFun f ts) requested out"
 and domain: "D ''2:=..'' [LPIFun f ts,requested]"
 and contract: "lp_answer_contract (lpp_domain_answers P B U D)
   ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) R t ret"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,requested])#gs),eta)#saved) R t ret"
proof (rule lp_answer_contract_intro)
 let ?T = "lpp_domain_answers P B U D"
 fix event tt
 assume step: "?T
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,requested])#gs),eta)#saved) event tt"
 have actual: "lpp_answer_transition P B U
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,requested])#gs),eta)#saved) event tt"
  using step domain by (auto simp: lpp_domain_answers_def)
 have no_answer: "event=None" and cover: "tt=[] \<or>
   lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) event tt"
  using lpp_univ_uses_shared_equality[OF selected coverage actual] by auto
 have child: "lp_answer_contract ?T tt R t ret"
 proof (cases "tt=[]")
  case True
  have empty: "lp_answer_contract ?T [] R t ret"
  proof (rule lp_answer_contract_intro)
   fix ev :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and us
   assume "?T [] ev us"
   then have "([],map fst us)\<in>lpp_atomic_source P B U"
    by (auto simp: lpp_domain_answers_def dest: lpp_answer_transition_erases)
   then show "(\<forall>rho. ev=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T us R t ret"
    by (simp add: lpp_atomic_source_empty)
  qed
  show ?thesis using empty True by simp
 next
  case False
  have equality: "lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) event tt"
   using cover False by simp
  have normalized: "?T
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) event tt"
   unfolding lpp_domain_answers_def by (intro disjI1 lpp_answer_transition.base[OF _ equality])
    (simp add: lpp_builtin_active_def)
  show ?thesis by (rule lp_answer_contract_child[OF contract normalized])
 qed
 show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T tt R t ret"
  using child no_answer by simp
qed

lemma lpp_univ_variable_input_stops:
 assumes selected: "(''2:=..'',2)\<in>B"
 and coverage: "\<And>out. U ''2:=..'' [LPIVar x,requested] out \<Longrightarrow>
   lpp_univ_view_outcome names (LPIVar x) requested out"
 and step: "lpp_answer_transition P B U
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIVar x,requested])#gs),eta)#saved) event tt"
 shows "event=None \<and> tt=[]"
proof -
 have only_error: "\<And>out. U ''2:=..'' [LPIVar x,requested] out \<Longrightarrow> out=LPPBuiltinError"
  using coverage by fastforce
 show ?thesis using step
  by (cases rule: lpp_answer_transition.cases)
   (use selected in \<open>auto simp: lpp_builtin_active_def numeral_2_eq_2 dest: only_error\<close>)
qed

lemma lpp_univ_view_normalized_contract:
 fixes P :: "(string,string) lp_cut_program"
 and eta :: "'v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and ret :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) \<Rightarrow> 'r"
 and R :: "'r rel" and t :: "'r"
 assumes selected: "(''2:=..'',2)\<in>B"
 and coverage: "\<And>out. U ''2:=..'' [input_value,requested] out \<Longrightarrow>
   lpp_univ_view_outcome names input_value requested out"
 and domain: "D ''2:=..'' [input_value,requested]"
 and contracts: "\<And>f ts. input_value=LPIFun f ts \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
   ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) R t ret"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [input_value,requested])#gs),eta)#saved) R t ret"
proof (cases input_value)
 case (LPIFun f ts)
 show ?thesis unfolding LPIFun
  apply (rule lpp_univ_normalized_contract[where names=names])
     apply (rule selected)
    apply (use coverage in \<open>simp add: LPIFun\<close>)
   apply (rule domain[unfolded LPIFun])
  by (rule contracts[OF LPIFun])
next
 case (LPIVar x)
 let ?T = "lpp_domain_answers P B U D"
 show ?thesis
 proof (rule lp_answer_contract_intro)
  fix event tt
  assume step: "?T ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [input_value,requested])#gs),eta)#saved) event tt"
  have actual: "lpp_answer_transition P B U
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIVar x,requested])#gs),eta)#saved) event tt"
   using step domain by (auto simp: lpp_domain_answers_def LPIVar)
  have stopped: "event=None" "tt=[]"
   using lpp_univ_variable_input_stops[OF selected coverage[unfolded LPIVar] actual] by auto
  have empty: "lp_answer_contract ?T [] R t ret"
  proof (rule lp_answer_contract_intro)
   fix ev :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and us
   assume "?T [] ev us"
   then have "([],map fst us)\<in>lpp_atomic_source P B U"
    by (auto simp: lpp_domain_answers_def dest: lpp_answer_transition_erases)
   then show "(\<forall>rho. ev=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T us R t ret"
    by (simp add: lpp_atomic_source_empty)
  qed
  show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T tt R t ret"
   using stopped empty by simp
 qed
qed

ML \<open>
val checked = [@{thm lpp_univ_view_normalized_contract}, @{thm lpp_univ_variable_input_stops}, @{thm lpp_univ_normalized_contract}, @{thm lpp_univ_uses_shared_equality}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ normalization dependency" else ();
\<close>
end
