theory LP_Prolog_Scalar_Domain_Prefix
 imports LP_Prolog_Scalar_Domain_Assignment
begin

definition lpp_recurrent_fixed_table where
 "lpp_recurrent_fixed_table domains x =
   (case domains x of Some (LPPRecurrentFixed v) \<Rightarrow> Some v | _ \<Rightarrow> None)"
lemma lpp_recurrent_fixed_parameters:
 assumes environment: "lpp_recurrent_domain_environment operation domains eta"
   and found: "lpp_recurrent_fixed_table domains x=Some v"
 shows "lpp_stable_scalar_evaluation operation (eta x) (lpp_machine_value v)"
proof -
 have entry: "domains x=Some (LPPRecurrentFixed v)"
   using found by (auto simp: lpp_recurrent_fixed_table_def
     split: option.splits lpp_recurrent_scalar_domain.splits)
 have "\<exists>w. lpp_recurrent_scalar_member (LPPRecurrentFixed v) w \<and>
   lpp_stable_scalar_evaluation operation (eta x) (lpp_machine_value w)"
   using environment entry unfolding lpp_recurrent_domain_environment_def by blast
 then show ?thesis by auto
qed

datatype lpp_domain_prefix = LPPDomainSet string lpp_scalar_template | LPPDomainGuard lpp_scalar_guard
fun lpp_domain_prefix_goal where
 "lpp_domain_prefix_goal (LPPDomainSet x e) = LPCAtom (Fun (LPCUser ''2:is'') [Var x,lpp_scalar_template_term e])"
| "lpp_domain_prefix_goal (LPPDomainGuard g) = lpp_scalar_guard_goal g"
fun lpp_domain_prefix_check where
 "lpp_domain_prefix_check H K domains [] = True"
| "lpp_domain_prefix_check H K domains (LPPDomainGuard g#ops) =
   (lpp_scalar_guard_check (lpp_recurrent_fixed_table domains) g=Some True \<and>
    lpp_domain_prefix_check H K domains ops)"
| "lpp_domain_prefix_check H K domains (LPPDomainSet x e#ops) =
   (x\<notin>set H \<and> x\<notin>set K \<and>
    (case lpp_recurrent_template_domain domains e of None \<Rightarrow> False
     | Some d \<Rightarrow> lpp_domain_prefix_check H (x#K) (domains(x:=Some d)) ops))"
fun lpp_domain_prefix_known where
 "lpp_domain_prefix_known K [] = K"
| "lpp_domain_prefix_known K (LPPDomainGuard g#ops) = lpp_domain_prefix_known K ops"
| "lpp_domain_prefix_known K (LPPDomainSet x e#ops) = lpp_domain_prefix_known (x#K) ops"
fun lpp_domain_prefix_domains where
 "lpp_domain_prefix_domains domains [] = domains"
| "lpp_domain_prefix_domains domains (LPPDomainGuard g#ops) = lpp_domain_prefix_domains domains ops"
| "lpp_domain_prefix_domains domains (LPPDomainSet x e#ops) =
    lpp_domain_prefix_domains (domains(x:=lpp_recurrent_template_domain domains e)) ops"

lemma lpp_domain_prefix_source_steps:
 assumes checked: "lpp_domain_prefix_check H K domains ops"
   and environment: "lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback) domains
     (lpp_recurrent_assignment_environment H K scalar_values eta)"
 shows "\<exists>result_values.
   lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback)
     (lpp_domain_prefix_domains domains ops)
     (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known K ops) result_values eta) \<and>
   (LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
       (lpp_recurrent_assignment_environment H K scalar_values eta)))
       (map lpp_domain_prefix_goal ops @ rest) @
     map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
       (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known K ops) result_values eta))) rest @
     map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es)\<in>
     (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>*"
 using checked environment
proof (induct ops arbitrary: K domains scalar_values)
 case Nil then show ?case by auto
next
 case (Cons op ops)
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
 let ?env = "lpp_recurrent_assignment_environment H K scalar_values eta"
 let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t ?env))
      (map lpp_domain_prefix_goal ops @ rest) @
      map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending"
 show ?case
 proof (cases op)
  case (LPPDomainGuard g)
  have guard: "lpp_scalar_guard_check (lpp_recurrent_fixed_table domains) g=Some True"
    and tail_checked: "lpp_domain_prefix_check H K domains ops"
    using Cons.prems by (auto simp: LPPDomainGuard)
  have parameters: "lpp_stable_scalar_evaluation ?operation (?env x) (lpp_machine_value v)"
    if found: "lpp_recurrent_fixed_table domains x=Some v" for x v
    by (rule lpp_recurrent_fixed_parameters[OF Cons.prems(2) found])
  have step: "(LPCGoals (lp_cut_map (\<lambda>t. lp_ieval t ?env) (lpp_scalar_guard_goal g)#?gs)#es,
      LPCGoals ?gs#es)\<in>?R"
    using lpp_scalar_guard_step[OF guard parameters, where gs="?gs" and es=es and P=P]
    by simp
  obtain result_values where env: "lpp_recurrent_domain_environment ?operation
      (lpp_domain_prefix_domains domains ops)
      (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known K ops) result_values eta)"
    and tail: "(LPCGoals ?gs#es,
     LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
       (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known K ops) result_values eta))) rest @
       map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es)\<in>?R\<^sup>*"
    using Cons.hyps[OF tail_checked Cons.prems(2)] by blast
  show ?thesis using env rtrancl_trans[OF r_into_rtrancl[OF step] tail]
    by (auto simp: LPPDomainGuard)
 next
  case (LPPDomainSet x e)
  obtain d where head_fresh: "x\<notin>set H" and local_fresh: "x\<notin>set K"
    and expression: "lpp_recurrent_template_domain domains e=Some d"
    and tail_checked: "lpp_domain_prefix_check H (x#K) (domains(x:=Some d)) ops"
    using Cons.prems by (auto simp: LPPDomainSet split: option.splits)
  obtain v where member: "lpp_recurrent_scalar_member d v"
    and evaluated: "lpp_stable_scalar_evaluation ?operation
       (lp_ieval (lpp_scalar_template_term e) ?env) (lpp_machine_value v)"
    using lpp_recurrent_template_sound[OF expression Cons.prems(2)] by blast
  let ?next_env = "lpp_recurrent_assignment_environment H (x#K) (scalar_values(x:=v)) eta"
  have next_environment: "lpp_recurrent_domain_environment ?operation (domains(x:=Some d)) ?next_env"
    by (rule lpp_recurrent_assignment_domains[OF Cons.prems(2) member])
  note step = lpp_recurrent_assignment_step[OF head_fresh local_fresh evaluated,
    where rest="map lpp_domain_prefix_goal ops @ rest" and pending=pending and es=es and P=P]
  obtain result_values where env: "lpp_recurrent_domain_environment ?operation
      (lpp_domain_prefix_domains (domains(x:=Some d)) ops)
      (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known (x#K) ops) result_values eta)"
    and tail: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t ?next_env))
       (map lpp_domain_prefix_goal ops @ rest) @
       map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,
     LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
       (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known (x#K) ops) result_values eta))) rest @
       map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es)\<in>?R\<^sup>*"
    using Cons.hyps[OF tail_checked next_environment] by blast
  show ?thesis using env rtrancl_trans[OF r_into_rtrancl[OF step] tail]
    by (auto simp: LPPDomainSet expression)
 qed
qed

ML \<open>
val checked = [@{thm lpp_domain_prefix_source_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar domain prefix dependency" else ();
\<close>
end
