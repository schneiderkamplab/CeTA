theory LP_Prolog_Scalar_Recurrence_Steps
 imports LP_Prolog_Scalar_Recurrence_Guards LP_Cut_Fresh_Head_Resolution
begin

lemma lpp_scalar_guard_step:
 assumes checked: "lpp_scalar_guard_check value_table g=Some held"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
 shows "(LPCGoals (lp_cut_map (\<lambda>t. lp_ieval t eta) (lpp_scalar_guard_goal g)#gs)#es,
   if held then LPCGoals gs#es else es) \<in>
   lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 let ?U = "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)"
 let ?f = "lpp_scalar_guard_symbol g"
 let ?ts = "map (\<lambda>t. lp_ieval t eta) (lpp_scalar_guard_terms g)"
 have outcome: "?U ?f ?ts (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
   by (rule lpp_scalar_guard_sound[OF checked parameters])
 have selected: "(?f,length ?ts)\<in>lpp_builtin_signature"
   using lpp_scalar_guard_checked_signature[OF checked] by simp
 show ?thesis
   using lpp_atomic_source.success[where U="?U" and f="?f" and ts="?ts" and sigma=LPIVar
     and P=P and B=lpp_builtin_signature and gs=gs and es=es]
     lpp_atomic_source.failure[where U="?U" and f="?f" and ts="?ts"
     and P=P and B=lpp_builtin_signature and gs=gs and es=es]
     outcome selected
   by (cases held) (auto simp: lpp_scalar_guard_goal_def lp_prolog_source_def lpp_builtin_active_def)
qed

lemma lpp_scalar_cut_step:
 "(LPCGoals (LPCCut mark#gs)#es,LPCGoals gs#lp_cut_prune mark es)\<in>lpp_builtin_source P U"
 by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def
   intro: lp_cut_mgu_source.admin)

datatype lpp_scalar_prefix = LPPScalarPrefixGuard lpp_scalar_guard | LPPScalarPrefixCut
fun lpp_scalar_prefix_goal where
 "lpp_scalar_prefix_goal (LPPScalarPrefixGuard g) = lpp_scalar_guard_goal g"
| "lpp_scalar_prefix_goal LPPScalarPrefixCut = LPCCut 0"
fun lpp_scalar_prefix_check where
 "lpp_scalar_prefix_check value_table (LPPScalarPrefixGuard g) = (lpp_scalar_guard_check value_table g=Some True)"
| "lpp_scalar_prefix_check value_table LPPScalarPrefixCut = True"

lemma lpp_scalar_successful_prefix:
 assumes checked: "list_all (lpp_scalar_prefix_check value_table) actions"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
 shows "\<exists>saved. (LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t eta))
     (map lpp_scalar_prefix_goal actions) @ gs)#es,LPCGoals gs#saved)\<in>
     (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>*"
 using checked
proof (induct actions arbitrary: es)
 case Nil show ?case by auto
next
 case (Cons action actions)
 have tail: "list_all (lpp_scalar_prefix_check value_table) actions"
   using Cons.prems by simp
 let ?rest = "map (lp_cut_bind mark (\<lambda>t. lp_ieval t eta)) (map lpp_scalar_prefix_goal actions) @ gs"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 show ?case
 proof (cases action)
  case (LPPScalarPrefixGuard g)
  have checked: "lpp_scalar_guard_check value_table g=Some True"
    using Cons.prems by (simp add: LPPScalarPrefixGuard)
  have step: "(LPCGoals (lp_cut_bind mark (\<lambda>t. lp_ieval t eta) (lpp_scalar_guard_goal g)#?rest)#es,
      LPCGoals ?rest#es)\<in>?R"
    using lpp_scalar_guard_step[OF checked parameters, where gs="?rest" and es=es and P=P]
    by (simp add: lpp_scalar_guard_goal_def)
  obtain saved where steps: "(LPCGoals ?rest#es,LPCGoals gs#saved)\<in>?R\<^sup>*"
    using Cons.hyps[OF tail] by blast
  show ?thesis using rtrancl_trans[OF r_into_rtrancl[OF step] steps]
    by (auto simp: LPPScalarPrefixGuard)
 next
  case LPPScalarPrefixCut
  have step: "(LPCGoals (LPCCut mark#?rest)#es,LPCGoals ?rest#lp_cut_prune mark es)\<in>?R"
    by (rule lpp_scalar_cut_step)
  obtain saved where steps: "(LPCGoals ?rest#lp_cut_prune mark es,LPCGoals gs#saved)\<in>?R\<^sup>*"
    using Cons.hyps[OF tail, of "lp_cut_prune mark es"] by blast
  show ?thesis using rtrancl_trans[OF r_into_rtrancl[OF step] steps]
    by (auto simp: LPPScalarPrefixCut)
 qed
qed

ML \<open>
val checked = [@{thm lpp_scalar_guard_step}, @{thm lpp_scalar_cut_step}, @{thm lpp_scalar_successful_prefix}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence source-step dependency" else ();
\<close>
end
