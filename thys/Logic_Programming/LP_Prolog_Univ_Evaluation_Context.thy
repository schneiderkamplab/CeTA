theory LP_Prolog_Univ_Evaluation_Context
 imports LP_Prolog_Univ_Context LP_Prolog_Univ_Evaluation_Initialization LP_Prolog_Evaluation_Functor_Link
begin

lemma lpp_univ_evaluation_initialized_state:
 fixes names :: "string lp_cut_symbol \<Rightarrow> string lp_cut_symbol"
 assumes checked: "lpp_check_univ_initialization value_variable name_variable arguments_variable input_template
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,requested])#gs),active)#saved) source_context source_functors"
 and input: "lp_ieval input_template eta=LPIFun f ts"
 and context_held: "lpp_evaluation_context_holds E SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 defines "extended \<equiv> eta(value_variable:=LPIFun f ts,
    name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)"
 shows "lpc_return_eval extended
   (lpp_univ_projected_state input_template requested gs active saved value_variable name_variable arguments_variable) =
  ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
    LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
    map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
proof -
 have same: "lpc_return_eval extended
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,requested])#gs),active)#saved) =
   lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,requested])#gs),active)#saved)"
  unfolding extended_def by (rule lpp_univ_evaluation_initialization_sound(1)[OF checked input context_held functors])
 have different: "value_variable\<noteq>name_variable" "value_variable\<noteq>arguments_variable" "name_variable\<noteq>arguments_variable"
  using checked by (auto simp: lpp_check_univ_initialization_def)
 have kept_input: "lp_ieval input_template extended=lp_ieval input_template eta"
 and kept_requested: "lp_ieval requested extended=lp_ieval requested eta"
 and kept_goals: "map (lp_cut_map (\<lambda>t. lp_ieval t extended)) gs=map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
 and kept_active: "lpc_return_env active extended=lpc_return_env active eta"
 and kept_saved: "lpc_return_eval extended saved=lpc_return_eval eta saved"
  using same by (auto simp: lpc_return_eval_def)
 have fields: "extended value_variable=LPIFun f ts" "extended name_variable=LPIFun (names f) []"
   "extended arguments_variable=lpp_argument_list ts"
  using different by (simp_all add: extended_def)
 show ?thesis
  by (simp add: lpc_return_eval_def kept_input kept_requested kept_goals kept_active
    kept_saved[unfolded lpc_return_eval_def] input fields)

qed

definition lpp_check_univ_evaluation_context where
 "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved value_variable name_variable arguments_variable middle =
  (ss=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,requested])#gs),active)#saved) \<and>
   lpp_check_univ_view_domain F input_template requested \<and>
   lpp_check_univ_initialization value_variable name_variable arguments_variable input_template ss source_context source_functors \<and>
   (\<forall>x\<in>set [value_variable,name_variable,arguments_variable].
      x\<notin>set (lpcn_vars nd) \<and> x\<notin>set (lpcn_ground nd) \<and> x\<notin>set F \<and>
      list_all (lpp_fresh_guard x) (lpcn_guards nd)) \<and>
   lpcl_swaps middle=[] \<and>
   lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd
    (lpp_univ_projected_state input_template requested gs active saved value_variable name_variable arguments_variable)
    (lpp_univ_projected_ground (lpcn_ground nd) input_template name_variable arguments_variable)
    (lpcn_guards nd) [] F source_context
    (LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable)#source_functors) middle)"

lemma lpp_univ_evaluation_context_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes contract: "lpp_eval_integer_contract TYPE(string) E"
 and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved value_variable name_variable arguments_variable middle"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and context_held: "lpp_evaluation_context_holds E SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and selected: "(''2:=..'',2)\<in>B"
 and domain: "\<And>a b. lpp_univ_view_domain a b \<Longrightarrow> D ''2:=..'' [a,b]"
 and coverage: "\<And>a b out. lpp_univ_view_domain a b \<Longrightarrow> U ''2:=..'' [a,b] out \<Longrightarrow>
    lpp_univ_view_outcome names a b out"
 and lower: "\<And>rho.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q \<Longrightarrow>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
    lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
    lpp_evaluation_context_holds E SP (contexts!lpcl_target middle) rho \<Longrightarrow>
    list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D) (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
 shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_return_eval eta ss) R t ret"
proof -
 let ?T = "lpp_domain_answers P B U D"
 let ?synthetic = "lpp_univ_projected_state input_template requested gs active saved value_variable name_variable arguments_variable"
 let ?observed = "LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable)#source_functors"
 let ?G = "lpp_univ_projected_ground (lpcn_ground nd) input_template name_variable arguments_variable"
 have shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,requested])#gs),active)#saved)"
 and init: "lpp_check_univ_initialization value_variable name_variable arguments_variable input_template ss source_context source_functors"
 and dom_check: "lpp_check_univ_view_domain F input_template requested"
 and fresh: "\<forall>x\<in>set [value_variable,name_variable,arguments_variable].
      x\<notin>set (lpcn_vars nd) \<and> x\<notin>set (lpcn_ground nd) \<and> x\<notin>set F \<and>
      list_all (lpp_fresh_guard x) (lpcn_guards nd)"
 and swaps: "lpcl_swaps middle=[]"
 and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ?synthetic ?G
    (lpcn_guards nd) [] F source_context ?observed middle"
  using checked by (auto simp: lpp_check_univ_evaluation_context_def)
 have admitted: "lpp_univ_view_domain (lp_ieval input_template eta) (lp_ieval requested eta)"
  by (rule lpp_check_univ_view_domain_sound[OF dom_check free])
 have contracts: "lp_answer_contract ?T
   ((LPCGoals (LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
  if input: "lp_ieval input_template eta=LPIFun f ts" for f ts
 proof -
  let ?nu = "eta(value_variable:=LPIFun f ts,name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)"
  have distinct: "name_variable\<noteq>arguments_variable" using init by (simp add: lpp_check_univ_initialization_def)
  have knowledge_fresh: "\<forall>x\<in>set [value_variable,name_variable,arguments_variable].
      x\<notin>set (lpcn_ground nd) \<and> x\<notin>set F \<and> list_all (lpp_fresh_guard x) (lpcn_guards nd)"
   using fresh by auto
  have base_known: "lp_cut_knowledge (insert name_variable (set (lpcn_ground nd))) (lpcn_guards nd) ?nu"
  and base_free: "lpc_free_knowledge (set F) ?nu"
   using lpp_univ_initialization_knowledge[OF knowledge_fresh distinct known free, of f ts names] by auto
  have extended_known: "lp_cut_knowledge (set ?G) (lpcn_guards nd) ?nu"
  proof (cases "vars_term input_template \<subseteq> set (lpcn_ground nd)")
   case True
   have ground_input: "lp_seg_ground (lp_ieval input_template eta)"
    using known True by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
   have ground: "lp_seg_ground (LPIFun f ts)" using ground_input input by simp
   show ?thesis using lpp_univ_initialization_ground_arguments[OF knowledge_fresh distinct known free ground, of names]
    by (simp add: lpp_univ_projected_ground_def True insert_commute)
  next
   case False then show ?thesis using base_known by (simp add: lpp_univ_projected_ground_def)
  qed
  have old: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)"
   using fresh by (auto intro!: map_cong)
  have context_extended: "lpp_evaluation_context_holds E SP source_context ?nu"
   by (rule lpp_univ_evaluation_initialization_sound(2)[OF init input context_held functors])
  have observed_extended: "list_all (lpp_functor_fact_holds names ?nu) ?observed"
   by (rule lpp_univ_evaluation_initialization_sound(3)[OF init input context_held functors])
  have equations: "lp_equations [] ?nu" by (simp add: lp_equations_def)
  obtain rho where same: "lpc_return_eval ?nu ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
   and target_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
   and target_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
   and target_context: "lpp_evaluation_context_holds E SP (contexts!lpcl_target middle) rho"
   and target_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
   and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
   using lpp_evaluation_functor_link_witness[OF contract evaluation program link equations old extended_known base_free context_extended observed_extended]
   by (simp add: swaps) blast
  have child: "lp_answer_contract ?T (lpc_return_eval ?nu ?synthetic) R t ret"
   using lower[OF edge target_known target_free target_context target_functors] by (simp only: same)
  have represented: "lpc_return_eval ?nu ?synthetic =
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
   by (rule lpp_univ_evaluation_initialized_state[OF init[unfolded shape] input context_held functors])
  show ?thesis by (rule lpp_reflexive_equality_contract_drop[OF child[unfolded represented]])
 qed
 have root: "lpc_return_eval eta ss =
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [lp_ieval input_template eta,lp_ieval requested eta])#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
  by (simp add: shape lpc_return_eval_def)
 show ?thesis unfolding root
  apply (rule lpp_univ_view_normalized_contract[where names=names])
     apply (rule selected)
    apply (rule coverage[OF admitted], assumption)
   apply (rule domain[OF admitted])
  by (rule contracts, assumption)
qed

lemma lpp_univ_evaluation_context_missing_domain_rejected:
 "\<not> lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd [] ss source_context source_functors
    (Var ''Input'') (Var ''List'') gs active saved value_variable name_variable arguments_variable middle"
 by (simp add: lpp_check_univ_evaluation_context_def)

lemma lpp_univ_evaluation_context_alias_rejected:
 "\<not> lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved x x arguments_variable middle"
 by (simp add: lpp_check_univ_evaluation_context_def lpp_check_univ_initialization_def)

lemma lpp_univ_evaluation_context_missing_child_rejected:
 "\<not> lpp_check_univ_evaluation_context T fs fuel Q nds [] contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved value_variable name_variable arguments_variable middle"
 by (simp add: lpp_check_univ_evaluation_context_def lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def lpc_check_return_table_link_def)

lemma lpp_univ_evaluation_context_saved_capture_rejected:
 "\<not> lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active [(LPCGoals [],[Var value_variable])]
    value_variable name_variable arguments_variable middle"
 by (auto simp: lpp_check_univ_evaluation_context_def lpp_check_univ_initialization_def lpp_fresh_return_def)

ML \<open>
val checked = [@{thm lpp_univ_evaluation_context_contract}, @{thm lpp_univ_evaluation_initialized_state}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted univ evaluation context dependency" else ();
\<close>
end
