theory LP_Prolog_Domain_Cut_Prefix
 imports LP_Prolog_Scalar_Domain_Iteration
begin

fun lpp_domain_cut_goals where
 "lpp_domain_cut_goals [] actions = map lpp_domain_prefix_goal actions"
| "lpp_domain_cut_goals (segment#segments) actions =
    map lpp_domain_prefix_goal segment @ LPCCut 0 # lpp_domain_cut_goals segments actions"

lemma lpp_domain_known_append:
 "lpp_domain_prefix_known K (xs@ys) = lpp_domain_prefix_known (lpp_domain_prefix_known K xs) ys"
 by (induct xs arbitrary: K) (auto, case_tac a, auto)
lemma lpp_domain_domains_append:
 "lpp_domain_prefix_domains domains (xs@ys) = lpp_domain_prefix_domains (lpp_domain_prefix_domains domains xs) ys"
 by (induct xs arbitrary: domains) (auto, case_tac a, auto)
lemma lpp_domain_check_append:
 "lpp_domain_prefix_check H K domains (xs@ys) =
   (lpp_domain_prefix_check H K domains xs \<and>
    lpp_domain_prefix_check H (lpp_domain_prefix_known K xs) (lpp_domain_prefix_domains domains xs) ys)"
 proof (induct xs arbitrary: K domains)
 case Nil then show ?case by simp
next
 case (Cons a xs)
 show ?case
 proof (cases a)
  case (LPPDomainGuard g) then show ?thesis by (simp add: Cons.hyps)
 next
  case (LPPDomainSet x e)
  show ?thesis by (cases "lpp_recurrent_template_domain domains e")
    (simp_all add: LPPDomainSet Cons.hyps fun_upd_def)
 qed
qed
lemmas lpp_domain_prefix_append = lpp_domain_known_append lpp_domain_domains_append lpp_domain_check_append

lemma lpp_domain_cut_source_steps:
 assumes checked: "lpp_domain_prefix_check H K domains (concat segments @ actions)"
 and environment: "lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback) domains
   (lpp_recurrent_assignment_environment H K scalar_values eta)"
 shows "\<exists>result_values saved.
   lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback)
     (lpp_domain_prefix_domains domains (concat segments @ actions))
     (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known K (concat segments @ actions)) result_values eta) \<and>
   (LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
      (lpp_recurrent_assignment_environment H K scalar_values eta)))
      (map (lp_cut_bind mark id) (lpp_domain_cut_goals segments actions) @ rest) @
      map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
      (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known K (concat segments @ actions)) result_values eta))) rest @
      map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#saved)\<in>
    (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>*"
 using checked environment
proof (induct segments arbitrary: K domains scalar_values es)
 case Nil
 note steps = lpp_domain_prefix_source_steps[OF Nil.prems(1)[simplified] Nil.prems(2),
   where rest=rest and pending=pending and es=es and P=P]
 show ?case using steps by (auto simp: map_map o_def lpp_domain_prefix_bind)
next
 case (Cons segment segments)
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
 let ?K = "lpp_domain_prefix_known K segment"
 let ?domains = "lpp_domain_prefix_domains domains segment"
 let ?tail = "map (lp_cut_bind mark id) (lpp_domain_cut_goals segments actions) @ rest"
 let ?pending = "map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending"
 have first: "lpp_domain_prefix_check H K domains segment"
 and later: "lpp_domain_prefix_check H ?K ?domains (concat segments @ actions)"
   using Cons.prems(1) by (simp_all add: lpp_domain_prefix_append)
 obtain middle_values where env: "lpp_recurrent_domain_environment ?operation ?domains
     (lpp_recurrent_assignment_environment H ?K middle_values eta)"
 and steps: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
    (lpp_recurrent_assignment_environment H K scalar_values eta)))
    (map lpp_domain_prefix_goal segment @ LPCCut mark # ?tail) @ ?pending)#es,
   LPCGoals (LPCCut mark # map (lp_cut_map (\<lambda>t. lp_ieval t
    (lpp_recurrent_assignment_environment H ?K middle_values eta))) ?tail @ ?pending)#es)\<in>?R\<^sup>*"
 using lpp_domain_prefix_source_steps[OF first Cons.prems(2),
   where rest="LPCCut mark # ?tail" and pending=pending and es=es and P=P] by auto
 let ?goals = "map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_recurrent_assignment_environment H ?K middle_values eta))) ?tail @ ?pending"
 have cut: "(LPCGoals (LPCCut mark # ?goals)#es,LPCGoals ?goals#lp_cut_prune mark es)\<in>?R"
   by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def
     intro: lp_cut_mgu_source.admin)
 obtain result_values saved where result:
   "lpp_recurrent_domain_environment ?operation
     (lpp_domain_prefix_domains ?domains (concat segments @ actions))
     (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known ?K (concat segments @ actions)) result_values eta)"
 and tail: "(LPCGoals ?goals#lp_cut_prune mark es,
   LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
     (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known ?K (concat segments @ actions)) result_values eta))) rest @ ?pending)#saved)\<in>?R\<^sup>*"
   using Cons.hyps[OF later env, where es="lp_cut_prune mark es"] by blast
 note combined = rtrancl_trans[OF steps rtrancl_trans[OF r_into_rtrancl[OF cut] tail]]
 show ?case using result combined
   by (auto simp: lpp_domain_prefix_append map_map o_def id_def lpp_domain_prefix_bind; blast)
qed

ML \<open>
val checked = [@{thm lpp_domain_cut_source_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted cut-prefix dependency" else ();
\<close>
end
