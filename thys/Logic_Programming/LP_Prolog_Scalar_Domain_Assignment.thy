theory LP_Prolog_Scalar_Domain_Assignment
 imports LP_Prolog_Scalar_Domain_Expressions LP_Prolog_Scalar_Recurrence_Steps LP_Cut_Fresh_Head_Controls
begin

definition lpp_recurrent_assignment_environment where
 "lpp_recurrent_assignment_environment H K scalar_values eta x =
   (if x\<in>set K then lpp_machine_value (scalar_values x)
    else if x\<in>set H then lp_isubst (eta x) lpc_fresh_caller
    else lpc_fresh_local x)"

lemma lpp_recurrent_environment_initial:
 "lpp_recurrent_assignment_environment H [] scalar_values eta = lpc_fresh_head_environment H eta"
 by (rule ext) (simp add: lpp_recurrent_assignment_environment_def lpc_fresh_head_environment_def)

lemma lpp_recurrent_environment_assignment:
 assumes head_fresh: "x\<notin>set H" and local_fresh: "x\<notin>set K"
 shows "lp_isubst (lpp_recurrent_assignment_environment H K scalar_values eta y)
     (LPIVar(CHR ''1''#x := lpp_machine_value v)) =
   lpp_recurrent_assignment_environment H (x#K) (scalar_values(x:=v)) eta y"
 using head_fresh local_fresh
 by (auto simp: lpp_recurrent_assignment_environment_def lpp_machine_value_named
   lpc_fresh_local_assignment_preserves_caller lpc_fresh_local_assignment)

lemma lpp_recurrent_assignment_step:
 assumes head_fresh: "x\<notin>set H" and local_fresh: "x\<notin>set K"
   and evaluated: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lp_ieval (lpp_scalar_template_term e) (lpp_recurrent_assignment_environment H K scalar_values eta))
     (lpp_machine_value v)"
 shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
       (lpp_recurrent_assignment_environment H K scalar_values eta)))
     (LPCAtom (Fun (LPCUser ''2:is'') [Var x,lpp_scalar_template_term e])#rest) @
     map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,
   LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
       (lpp_recurrent_assignment_environment H (x#K) (scalar_values(x:=v)) eta))) rest @
     map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es)\<in>
   lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 let ?env = "lpp_recurrent_assignment_environment H K scalar_values eta"
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?mu = "LPIVar(CHR ''1''#x := lpp_machine_value v)"
 let ?f = "lpp_machine_name v"
 have evaluation: "lpp_stable_scalar_evaluation ?operation
     (lp_ieval (lpp_scalar_template_term e) ?env) (LPIFun (LPCUser ?f) [])"
   using evaluated by (simp only: lpp_machine_value_named)
 have assigned: "lpp_scalar_unifier (?env x) ?f=Some ?mu"
   using head_fresh local_fresh
   by (simp add: lpp_recurrent_assignment_environment_def lpc_fresh_local_def lpp_machine_value_named)
 have outcome: "lpp_stable_source_builtin ?operation ''2:is''
     [?env x,lp_ieval (lpp_scalar_template_term e) ?env] (LPPBuiltinSuccess ?mu)"
   using lpp_stable_source_is_evaluated[OF lpp_binary64_profile_integer_compatible evaluation,
     where a="?env x"] assigned by simp
 have binding: "(\<lambda>y. lp_isubst (?env y) ?mu)=
     lpp_recurrent_assignment_environment H (x#K) (scalar_values(x:=v)) eta"
   by (rule ext, rule lpp_recurrent_environment_assignment[OF head_fresh local_fresh])
 have step: "(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'')
      [?env x,lp_ieval (lpp_scalar_template_term e) ?env])#
      (map (lp_cut_map (\<lambda>t. lp_ieval t ?env)) rest @
       map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending))#es,
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t ?mu))
      (map (lp_cut_map (\<lambda>t. lp_ieval t ?env)) rest @
       map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending))#es)\<in>
    lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
   using lpp_atomic_source.success[where U="lpp_stable_source_builtin ?operation"
     and f="''2:is''" and ts="[?env x,lp_ieval (lpp_scalar_template_term e) ?env]"
     and sigma="?mu" and P=P and B=lpp_builtin_signature and es=es
     and gs="map (lp_cut_map (\<lambda>t. lp_ieval t ?env)) rest @
       map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending"] outcome
   by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_builtin_signature_def)
 show ?thesis using step
   by (simp add: map_map lp_cut_map_comp lp_ieval_subst binding o_def
     lpc_fresh_local_assignment_preserves_caller)
qed

lemma lpp_recurrent_assignment_domains:
 assumes previous: "lpp_recurrent_domain_environment operation domains
     (lpp_recurrent_assignment_environment H K scalar_values eta)"
   and member: "lpp_recurrent_scalar_member d v"
 shows "lpp_recurrent_domain_environment operation (domains(x:=Some d))
   (lpp_recurrent_assignment_environment H (x#K) (scalar_values(x:=v)) eta)"
proof -
 have evaluated: "lpp_stable_scalar_evaluation operation (lpp_machine_value v) (lpp_machine_value v)"
   by (rule lpp_stable_scalar_evaluation.scalar[OF lpp_machine_scalar_fraction[OF lpp_recurrent_member_valid[OF member]]])
 show ?thesis unfolding lpp_recurrent_domain_environment_def
 proof (intro allI impI)
  fix y e
  assume found: "(domains(x:=Some d)) y=Some e"
  show "\<exists>w. lpp_recurrent_scalar_member e w \<and>
    lpp_stable_scalar_evaluation operation
      (lpp_recurrent_assignment_environment H (x#K) (scalar_values(x:=v)) eta y)
      (lpp_machine_value w)"
  proof (cases "y=x")
   case True
   show ?thesis using found member evaluated True
     by (auto simp: lpp_recurrent_assignment_environment_def)
  next
   case False
   have old: "domains y=Some e" using found False by simp
   have same: "lpp_recurrent_assignment_environment H (x#K) (scalar_values(x:=v)) eta y =
       lpp_recurrent_assignment_environment H K scalar_values eta y"
     using False by (simp add: lpp_recurrent_assignment_environment_def)
   show ?thesis unfolding same using previous old
     by (auto simp only: lpp_recurrent_domain_environment_def)
  qed
 qed
qed

ML \<open>
val checked = [@{thm lpp_recurrent_assignment_step}, @{thm lpp_recurrent_assignment_domains}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar domain assignment dependency" else ();
\<close>
end
