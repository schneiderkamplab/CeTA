theory Global_Copy_Invariant_Check
 imports Global_Functor_Copy_Contract_Check
begin

lemma copy_output_facts_from_invariant:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter)
   specs rest oi hi [(goals,env)]"
 and coordinate: "env (Inl oi) = output_value"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and leaf_slot: "(hi,Fun (Inr ()) []) \<in> set specs"
 and history: "(hi,initial_tree) \<in> set specs"
 shows "lpp_caller_output_mode output_value \<and>
   lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
proof -
 have base: "lpp_observer_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest [(goals,env)]"
  using invariant by (simp add: lpp_observer_output_invariant_def)
 have same: "env (Inr hi) = output_value"
  using invariant coordinate by (simp add: lpp_observer_output_invariant_def lpp_observer_output_alias_def)
 have ground: "vars_term initial_parameter = {}"
  using tracked by (simp add: lpp_runtime_parameter_def)
 have mode: "lpp_caller_output_mode (env (Inr hi))"
  by (rule lpp_observer_restricted_output_mode[OF base leaf_slot _
    lpp_parameter_leaf_templates_ground[OF ground]]) simp
 have effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree (env (Inr hi))"
  using base history by (auto simp: lpp_observer_invariant_def lpp_leaf_stack_invariant_def lpc_reinterface_def list_all_iff)
 show ?thesis using mode effect same by simp
qed

theorem invariant_simple_copy_caller_contract:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
   [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)]"
 and head: "fst (P!c) = Fun p [Fun nil [],Var n,Var n]"
 and body: "snd (P!c) = [LPCCut 0]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and observed: "observed_leaf_coordinate encode B parameter_tree parameter shadow"
 and clause: "((source_symbol,map Var [x0,x1,x2,s0,sn,s2]),[(target_symbol,map Var [rn,sn])]) \<in> set Q"
 and distinct: "distinct [x0,x1,x2,s0,sn,s2,rn]"

 and helper_coordinate: "env (Inl oi) = output_value"
 and leaf_slot: "(hi,Fun (Inr ()) []) \<in> set specs"
 and history: "(hi,initial_tree) \<in> set specs"
 and caller: "\<And>rho. rho hi = parameter \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (rho hi) shadow \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(target_symbol,[parameter,shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
    [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)])) (lp_ild Q)
   [(source_symbol,[input_value,parameter,output_value,input_shadow,shadow,output_shadow])] returned"

proof -
 have facts: "lpp_caller_output_mode output_value \<and>
   lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
  by (rule copy_output_facts_from_invariant[OF invariant helper_coordinate tracked leaf_slot history])
 have mode: "lpp_caller_output_mode output_value" and effect:
  "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
  using facts by blast+
 show ?thesis by (rule global_simple_copy_caller_contract[OF invariant head body spine tracked mode covered effect observed clause distinct helper_coordinate caller])
qed

theorem invariant_functor_copy_caller_contract:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
   [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)]"
 and head: "fst (P!c) = Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]"
 and body: "snd (P!c) = [LPCCut 0]"
 and spine: "lpp_finite_spine cons (LPCUser ''0:prolog_data_5b5d'') input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and observed: "observed_leaf_coordinate encode B parameter_tree parameter shadow"
 and functor_fact: "lpp_functor_observation names functor_value name_value input_value"
 and name_observed: "observed_leaf_coordinate encode C name_tree name_value name_shadow"
 and functor_observed: "observed_leaf_coordinate encode D functor_tree functor_value functor_shadow"
 and clause: "((source_symbol,map Var [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4]),
   [(target_symbol,map Var [rn,x3,y,sn,s3,sy])]) \<in> set Q"
 and distinct: "distinct [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4,y,sy]"
 and helper_coordinate: "env (Inl oi) = output_value"
 and leaf_slot: "(hi,Fun (Inr ()) []) \<in> set specs"
 and history: "(hi,initial_tree) \<in> set specs"
 and caller: "\<And>rho. rho hi = parameter \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (rho hi) shadow \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(target_symbol,[parameter,name_value,functor_value,shadow,name_shadow,functor_shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
    [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)])) (lp_ild Q)
   [(source_symbol,[input_value,parameter,output_value,name_value,functor_value,input_shadow,shadow,output_shadow,name_shadow,functor_shadow])] returned"

proof -
 have facts: "lpp_caller_output_mode output_value \<and>
   lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
  by (rule copy_output_facts_from_invariant[OF invariant helper_coordinate tracked leaf_slot history])
 have mode: "lpp_caller_output_mode output_value" and effect:
  "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
  using facts by blast+
 show ?thesis by (rule global_functor_copy_caller_contract[OF invariant head body spine tracked mode covered effect observed functor_fact name_observed functor_observed clause distinct helper_coordinate caller])
qed


lemma free_helper_mode_control:
 "lpp_caller_output_mode (LPIVar x :: (string lp_cut_symbol,string) lp_iterm)"
 by (simp add: lpp_caller_output_mode_def)

lemma compound_helper_mode_control:
 "lpp_caller_output_mode (LPIFun (LPCUser ''f'') [LPIFun (LPCUser ''a'') []] :: (string lp_cut_symbol,string) lp_iterm)"
 by (simp add: lpp_caller_output_mode_def)

lemma partial_helper_mode_rejected:
 "\<not> lpp_caller_output_mode (LPIFun (LPCUser ''f'') [LPIVar x] :: (string lp_cut_symbol,string) lp_iterm)"
 by (simp add: lpp_caller_output_mode_def lp_seg_ground.simps)

ML \<open>
val checked = @{thms copy_output_facts_from_invariant invariant_simple_copy_caller_contract invariant_functor_copy_caller_contract
 free_helper_mode_control compound_helper_mode_control partial_helper_mode_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted invariant copy contracts" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-copy-invariant/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Mode and output effect derived from joint invariant; caller contract remains explicit.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_COPY_INVARIANT_KERNEL_CHECKED";
\<close>
end
