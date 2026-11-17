theory LP_Prolog_Univ_Initialization
 imports LP_Prolog_Functor_Link LP_Prolog_Univ_Normalization LP_Prolog_Context_Is
begin

text \<open>Initialize the projected value and its two fields from an actual
constructor input. The fresh variables are observation names, not substitutions
on runtime variables. Original saved states and prior contexts remain intact.\<close>

definition lpp_functor_fact_fresh where
 "lpp_functor_fact_fresh x observation =
  (\<forall>t\<in>set (lpp_functor_fact_terms observation). x\<notin>vars_term t)"

lemma lpp_functor_fact_fresh_eval:
 "lpp_functor_fact_fresh x observation \<Longrightarrow>
  lpp_functor_fact_holds names (eta(x:=v)) observation = lpp_functor_fact_holds names eta observation"
 by (rule lpp_functor_fact_environment_cong)
  (auto simp: lpp_functor_fact_fresh_def intro: lpp_fresh_term_eval)

definition lpp_check_univ_initialization where
 "lpp_check_univ_initialization value_variable name_variable arguments_variable input_template ss source_context source_functors =
  (distinct [value_variable,name_variable,arguments_variable] \<and>
   (\<forall>x\<in>set [value_variable,name_variable,arguments_variable].
    x\<notin>vars_term input_template \<and> lpp_fresh_return x ss \<and>
    lpp_context_fresh x source_context \<and> list_all (lpp_functor_fact_fresh x) source_functors))"

lemma lpp_univ_initialization_sound:
 fixes names :: "string lp_cut_symbol \<Rightarrow> string lp_cut_symbol"
 assumes checked: "lpp_check_univ_initialization value_variable name_variable arguments_variable input_template ss source_context source_functors"
 and input: "lp_ieval input_template eta=LPIFun f ts"
 and known_context: "lpp_source_context_holds P source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 defines "extended \<equiv> eta(value_variable:=LPIFun f ts,
    name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)"
 shows "lpc_return_eval extended ss=lpc_return_eval eta ss"
 and "lpp_source_context_holds P source_context extended"
 and "list_all (lpp_functor_fact_holds names extended)
   (LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable)#source_functors)"
 and "lp_ieval input_template extended=lp_ieval (Var value_variable) extended"
proof -
 have different: "value_variable\<noteq>name_variable" "value_variable\<noteq>arguments_variable" "name_variable\<noteq>arguments_variable"
 and state_fresh: "lpp_fresh_return value_variable ss" "lpp_fresh_return name_variable ss" "lpp_fresh_return arguments_variable ss"
 and context_fresh: "lpp_context_fresh value_variable source_context" "lpp_context_fresh name_variable source_context" "lpp_context_fresh arguments_variable source_context"
 and input_fresh: "value_variable\<notin>vars_term input_template" "name_variable\<notin>vars_term input_template" "arguments_variable\<notin>vars_term input_template"
 and previous_fresh: "list_all (lpp_functor_fact_fresh value_variable) source_functors"
   "list_all (lpp_functor_fact_fresh name_variable) source_functors"
   "list_all (lpp_functor_fact_fresh arguments_variable) source_functors"
  using checked by (auto simp: lpp_check_univ_initialization_def)
 show "lpc_return_eval extended ss=lpc_return_eval eta ss"
  unfolding extended_def by (simp add: lpp_fresh_return_eval[OF state_fresh(1)]
   lpp_fresh_return_eval[OF state_fresh(2)] lpp_fresh_return_eval[OF state_fresh(3)])
 show "lpp_source_context_holds P source_context extended"
  using known_context unfolding extended_def by (simp add: lpp_context_fresh_eval[OF context_fresh(1)]
   lpp_context_fresh_eval[OF context_fresh(2)] lpp_context_fresh_eval[OF context_fresh(3)])
 have previous: "list_all (lpp_functor_fact_holds names extended) source_functors"
  using functors previous_fresh unfolding extended_def
  by (auto simp: list_all_iff lpp_functor_fact_fresh_eval)
 show "list_all (lpp_functor_fact_holds names extended)
   (LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable)#source_functors)"
  using previous different by (simp add: extended_def lpp_functor_observation_exact)
 show "lp_ieval input_template extended=lp_ieval (Var value_variable) extended"
  using different input unfolding extended_def by (simp add:
   lpp_fresh_term_eval[OF input_fresh(1)] lpp_fresh_term_eval[OF input_fresh(2)] lpp_fresh_term_eval[OF input_fresh(3)])
qed

lemma lpp_univ_initialization_alias_rejected:
 "\<not> lpp_check_univ_initialization x x y input_template ss source_context source_functors"
 by (simp add: lpp_check_univ_initialization_def)

lemma lpp_reflexive_equality_contract_drop:
 assumes contract: "lp_answer_contract (lpp_domain_answers P B U D)
   ((LPCGoals (LPCUnify a a#gs),eta)#saved) R t ret"
 shows "lp_answer_contract (lpp_domain_answers P B U D) ((LPCGoals gs,eta)#saved) R t ret"
proof -
 have identity: "lpc_mgu_unify a a gs LPIVar"
  by (auto simp: lpc_mgu_unify_def)
 have equality: "lpc_answer_transition P ((LPCGoals (LPCUnify a a#gs),eta)#saved)
   None ((LPCGoals gs,eta)#saved)"
  using lpc_answer_transition.unify[OF identity, of P eta saved] by simp
 have step: "lpp_domain_answers P B U D ((LPCGoals (LPCUnify a a#gs),eta)#saved)
   None ((LPCGoals gs,eta)#saved)"
  unfolding lpp_domain_answers_def by (intro disjI1 lpp_answer_transition.base[OF _ equality])
   (simp add: lpp_builtin_active_def)
 show ?thesis by (rule lp_answer_contract_child[OF contract step])
qed

lemma lpp_univ_two_equalities_contract:
 assumes selected: "(''2:=..'',2)\<in>B"
 and coverage: "\<And>out. U ''2:=..'' [LPIFun f ts,requested] out \<Longrightarrow>
   lpp_univ_decompose_outcome names (LPIFun f ts) requested out"
 and domain: "D ''2:=..'' [LPIFun f ts,requested]"
 and contract: "lp_answer_contract (lpp_domain_answers P B U D)
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify requested (lpp_argument_list (LPIFun (names f) [] # ts))#gs),eta)#saved) R t ret"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,requested])#gs),eta)#saved) R t ret"
 apply (rule lpp_univ_normalized_contract[where names=names])
    apply (rule selected)
   apply (rule coverage, assumption)
  apply (rule domain)
 by (rule lpp_reflexive_equality_contract_drop[OF contract])

lemma lpp_univ_initialization_fresh_checked:
 "lpp_check_univ_initialization ''Value'' ''Name'' ''Args'' (Var ''Input'')
   [(LPCGoals [],[Var ''Input''])] ([],[],[]) []"
 by (simp add: lpp_check_univ_initialization_def lpp_fresh_return_def lpp_context_fresh_def)

lemma lpp_univ_initialization_saved_capture_rejected:
 "\<not> lpp_check_univ_initialization ''Value'' ''Name'' ''Args'' (Var ''Input'')
   [(LPCGoals [],[Var ''Value''])] ([],[],[]) []"
 by (simp add: lpp_check_univ_initialization_def lpp_fresh_return_def)

lemma lpp_univ_initialization_prior_capture_rejected:
 "\<not> lpp_check_univ_initialization ''Value'' ''Name'' ''Args'' (Var ''Input'')
   [] ([],[],[]) [LPPFunctorFact (Var ''Old'') (Var ''Name'') (Var ''OldArgs'')]"
 by (simp add: lpp_check_univ_initialization_def lpp_fresh_return_def lpp_context_fresh_def lpp_functor_fact_fresh_def)

lemma lpp_fresh_observation_knowledge:
 "lp_cut_knowledge G guards eta \<Longrightarrow> x\<notin>G \<Longrightarrow>
  list_all (lpp_fresh_guard x) guards \<Longrightarrow>
  lp_cut_knowledge G guards (eta(x:=v))"
 by (auto simp: lp_cut_knowledge_def list_all_iff lpp_fresh_guard_eval)

lemma lpp_fresh_observation_free:
 "lpc_free_knowledge F eta \<Longrightarrow> x\<notin>F \<Longrightarrow>
  lpc_free_knowledge F (eta(x:=v))"
 by (auto simp: lpc_free_knowledge_def inj_on_def)

lemma lpp_univ_initialization_knowledge:
 fixes names :: "string lp_cut_symbol \<Rightarrow> string lp_cut_symbol"
 and f :: "string lp_cut_symbol" and ts :: "(string lp_cut_symbol,string) lp_iterm list"
 assumes fresh: "\<forall>x\<in>set [value_variable,name_variable,arguments_variable].
   x\<notin>G \<and> x\<notin>F \<and> list_all (lpp_fresh_guard x) guards"
 and distinct: "name_variable\<noteq>arguments_variable"
 and known: "lp_cut_knowledge G guards eta"
 and free: "lpc_free_knowledge F eta"
 defines "extended \<equiv> eta(value_variable:=LPIFun f ts,
    name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)"
 shows "lp_cut_knowledge (insert name_variable G) guards extended \<and> lpc_free_knowledge F extended"
proof -
 have keep_known: "lp_cut_knowledge G guards (nu(x:=v))"
  if "x\<in>set [value_variable,name_variable,arguments_variable]" "lp_cut_knowledge G guards nu" for x nu v
  by (rule lpp_fresh_observation_knowledge[OF that(2)]) (use fresh that(1) in auto)
 have keep_free: "lpc_free_knowledge F (nu(x:=v))"
  if "x\<in>set [value_variable,name_variable,arguments_variable]" "lpc_free_knowledge F nu" for x nu v
  by (rule lpp_fresh_observation_free[OF that(2)]) (use fresh that(1) in auto)
 have preserved: "lp_cut_knowledge G guards extended" "lpc_free_knowledge F extended"
  unfolding extended_def by (intro keep_known keep_free known free; simp)+
 have name_ground: "lp_seg_ground (extended name_variable)"
  using distinct by (auto simp: extended_def intro: lp_seg_ground.intros)
 show ?thesis using preserved name_ground by (auto simp: lp_cut_knowledge_def)
qed

lemma lpp_univ_argument_list_ground:
 "lp_seg_ground (LPIFun f ts) \<Longrightarrow> lp_seg_ground (lpp_argument_list ts)"
proof -
 assume ground: "lp_seg_ground (LPIFun f ts)"
 have "list_all lp_seg_ground ts" using ground by (auto elim: lp_seg_ground.cases)
 then show ?thesis by (induction ts) (auto intro: lp_seg_ground.intros)
qed

lemma lpp_univ_initialization_ground_arguments:
 fixes names :: "string lp_cut_symbol \<Rightarrow> string lp_cut_symbol"
 assumes fresh: "\<forall>x\<in>set [value_variable,name_variable,arguments_variable].
   x\<notin>G \<and> x\<notin>F \<and> list_all (lpp_fresh_guard x) guards"
 and distinct: "name_variable\<noteq>arguments_variable"
 and known: "lp_cut_knowledge G guards eta"
 and free: "lpc_free_knowledge F eta"
 and ground: "lp_seg_ground (LPIFun f ts)"
 defines "extended \<equiv> eta(value_variable:=LPIFun f ts,
    name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)"
 shows "lp_cut_knowledge (insert arguments_variable (insert name_variable G)) guards extended"
proof -
 have initialized: "lp_cut_knowledge (insert name_variable G) guards extended"
  using lpp_univ_initialization_knowledge[OF fresh distinct known free, of f ts names]
  by (simp add: extended_def)
 have args_ground: "lp_seg_ground (extended arguments_variable)"
  using lpp_univ_argument_list_ground[OF ground] by (simp add: extended_def)
 show ?thesis using initialized args_ground by (auto simp: lp_cut_knowledge_def)
qed

ML \<open>
val checked = @{thms lpp_univ_initialization_sound lpp_univ_two_equalities_contract lpp_univ_initialization_knowledge lpp_univ_initialization_ground_arguments};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ initialization dependency" else ();
\<close>
end
