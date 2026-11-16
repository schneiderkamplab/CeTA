theory LP_Prolog_Domain_Choice
 imports LP_Prolog_Guarded_Domain_Edge LP_Prolog_Domain_Graph
begin

fun lpp_domain_module_variables where
 "lpp_domain_module_variables (LPPDomainModule q obs sel H actions outputs recipes failures dest)=H"
fun lpp_domain_module_selection where
 "lpp_domain_module_selection (LPPDomainModule q obs sel H actions outputs recipes failures dest)=sel"
fun lpp_guarded_branch_check where
 "lpp_guarded_branch_check P interfaces gate (LPPDomainModule q obs sel H actions outputs recipes failures dest) =
   (dest<length interfaces \<and> failures=[] \<and>
    lpp_guarded_domain_edge_check P q obs sel H gate actions outputs recipes
      (fst (interfaces!dest)) (snd (interfaces!dest)))"
definition lpp_domain_choice_check where
 "lpp_domain_choice_check P interfaces gate other a b =
   (lpp_domain_module_q a=lpp_domain_module_q b \<and>
    lpp_domain_module_observations a=lpp_domain_module_observations b \<and>
    lpp_domain_module_variables a=lpp_domain_module_variables b \<and>
    lpp_domain_module_selection a=0 \<and> lpp_domain_module_selection b=1 \<and>
    lpp_domain_guard_total (lpp_scalar_value_table (lpp_domain_module_variables a)
      (lpp_domain_module_observations a)) gate \<and>
    lpp_domain_opposite_guards gate other \<and>
    lpp_guarded_branch_check P interfaces gate a \<and>
    lpp_guarded_branch_check P interfaces other b)"

lemma lpp_domain_choice_progress:
 assumes checked: "lpp_domain_choice_check P interfaces gate other a b"
 and observed: "lpp_domain_observations (lpp_binary64_profile_operation fallback)
   (lpp_domain_module_observations a) actuals"
 shows "\<exists>j next_args pending saved. j<length interfaces \<and>
   lpp_domain_observations (lpp_binary64_profile_operation fallback) (snd (interfaces!j)) next_args \<and>
   (LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_domain_module_q a)) actuals)#gs)#es,
    LPCGoals (LPCAtom (LPIFun (LPCUser (fst (interfaces!j))) next_args)#pending)#saved)\<in>
      (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 obtain q obs sel H actions outputs recipes failures dest where a:
   "a=LPPDomainModule q obs sel H actions outputs recipes failures dest" by (cases a) auto
 obtain q1 obs1 sel1 H1 actions1 outputs1 recipes1 failures1 dest1 where b:
   "b=LPPDomainModule q1 obs1 sel1 H1 actions1 outputs1 recipes1 failures1 dest1" by (cases b) auto
 have same: "q1=q" "obs1 = obs" "H1=H" "sel=0" "sel1=1"
 and total: "lpp_domain_guard_total (lpp_scalar_value_table H obs) gate"
 and opposite: "lpp_domain_opposite_guards gate other"
 and first: "lpp_guarded_domain_edge_check P q obs 0 H gate actions outputs recipes
    (fst (interfaces!dest)) (snd (interfaces!dest))"
 and second: "lpp_guarded_domain_edge_check P q obs 1 H other actions1 outputs1 recipes1
    (fst (interfaces!dest1)) (snd (interfaces!dest1))"
 and bounds: "dest<length interfaces" "dest1<length interfaces"
 using checked by (auto simp: lpp_domain_choice_check_def a b)
 have obs: "lpp_domain_observations (lpp_binary64_profile_operation fallback) obs actuals"
 using observed by (simp add: a)
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
 let ?domains = "lpp_scalar_value_table H obs"
 let ?eta = "lpp_partial_arguments H actuals"
 let ?table = "lpp_domain_concrete_table ?operation ?domains ?eta"
 let ?clauses = "lp_cut_slice P (LPCUser q) (length obs)"
 have lengths: "length H=length obs" and distinct: "distinct H"
   using first by (auto simp: lpp_guarded_domain_edge_check_def Let_def)
 have environment: "lpp_recurrent_domain_environment ?operation ?domains ?eta"
   by (rule lpp_domain_observed_environment[OF lengths distinct obs])
 have concrete: "\<exists>v. ?table x=Some v \<and> lpp_recurrent_scalar_member d v"
   if "?domains x=Some d" for x d
   using lpp_domain_concrete_member[OF environment that] by blast
 obtain held where guard: "lpp_scalar_guard_check ?table gate=Some held"
   using lpp_domain_guard_defined[where domains="?domains" and table="?table" and g=gate]
     total concrete by blast
 show ?thesis
 proof (cases held)
  case True
  have progress: "\<exists>next_args pending saved.
    lpp_domain_observations ?operation (snd (interfaces!dest)) next_args \<and>
    (LPCGoals (LPCAtom (LPIFun (LPCUser q) actuals)#gs)#es,
     LPCGoals (LPCAtom (LPIFun (LPCUser (fst (interfaces!dest))) next_args)#pending)#saved)\<in>?R\<^sup>+"
    by (rule lpp_guarded_domain_edge_progress[OF first obs]) (use guard True in auto)
  show ?thesis using progress bounds by (auto simp: a)
 next
  case False
  have other: "lpp_scalar_guard_check ?table other=Some True"
    using lpp_domain_guard_opposite[OF opposite, of "?table"] guard False by simp
  have actual_length: "length H=length actuals" using lengths obs
    by (simp add: lpp_domain_observations_def)
  have head: "lp_ieval (Fun (LPCUser q) (map Var H)) ?eta=LPIFun (LPCUser q) actuals"
    using lpp_partial_arguments_exact[OF actual_length distinct] by (simp add: map_map o_def)
  have parameters: "lpp_stable_scalar_evaluation ?operation (?eta x) (lpp_machine_value v)"
    if "?table x=Some v" for x v
    by (rule lpp_domain_concrete_parameters[OF environment that])
  have covered: "x\<in>set H" if "?table x=Some v" for x v
    using that lpp_scalar_table_covered[OF lengths]
    by (auto simp: lpp_domain_concrete_table_def split: option.splits)
  have failed: "(LPCClause (LPCAtom (LPIFun (LPCUser q) actuals)#gs) d mark#saved,saved)\<in>?R\<^sup>+"
    if member: "d\<in>set (take 1 ?clauses)" for d mark saved
  proof -
   have index: "?clauses!0<length P" and nonempty: "0<length ?clauses"
     and prefix: "take (Suc (length actions)) (snd (P!(?clauses!0)))=lpp_scalar_guard_goal gate # map lpp_domain_prefix_goal actions"
     and bound: "Suc (length actions)<length (snd (P!(?clauses!0)))"
     and head_clause: "fst (P!(?clauses!0))=Fun (LPCUser q) (map Var H)"
     using first by (auto simp: lpp_guarded_domain_edge_check_def Let_def)
   have selected: "d=?clauses!0" using member nonempty
     by (cases "?clauses") auto
   have body: "snd (P!d)=lpp_scalar_guard_goal gate # drop 1 (snd (P!d))"
     using prefix bound selected by (cases "snd (P!(?clauses!0))") auto
   have clause: "P!d=(Fun (LPCUser q) (map Var H),
     map lpp_scalar_guard_goal [] @ lpp_scalar_guard_goal gate # drop 1 (snd (P!d)))"
     using body head_clause selected by (cases "P!d") auto
   show ?thesis using lpp_scalar_failed_clause[OF index[folded selected] clause,
     where value_table="?table" and eta="?eta" and gs=gs and mark=mark and es=saved]
     guard False parameters covered head by auto
  qed
  have progress: "\<exists>next_args pending saved.
    lpp_domain_observations ?operation (snd (interfaces!dest1)) next_args \<and>
    (LPCGoals (LPCAtom (LPIFun (LPCUser q) actuals)#gs)#es,
     LPCGoals (LPCAtom (LPIFun (LPCUser (fst (interfaces!dest1))) next_args)#pending)#saved)\<in>?R\<^sup>+"
    by (rule lpp_guarded_domain_edge_progress[OF second obs other failed])
  show ?thesis using progress bounds by (auto simp: a)
 qed
qed

ML \<open>
val checked = [@{thm lpp_domain_choice_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted guarded source choice dependency" else ();
\<close>
end
