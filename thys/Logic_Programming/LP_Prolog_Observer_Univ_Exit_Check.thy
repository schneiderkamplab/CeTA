theory LP_Prolog_Observer_Univ_Exit_Check
 imports LP_Prolog_Observer_Frontier_Block
begin

fun lpp_observer_template_exit_goals where
 "lpp_observer_template_exit_goals [] = True"
| "lpp_observer_template_exit_goals (LPCUnify a b#gs) = False"
| "lpp_observer_template_exit_goals (LPCAtom (Var x)#gs) = False"
| "lpp_observer_template_exit_goals (LPCAtom (Fun (LPCUser f) ts)#gs) = (f\<noteq>''2:=..'')"
| "lpp_observer_template_exit_goals gs = True"

fun lpp_observer_template_exit_stack where
 "lpp_observer_template_exit_stack ((LPCGoals gs,env)#saved) = lpp_observer_template_exit_goals gs"
| "lpp_observer_template_exit_stack ss = True"

lemma lpp_observer_template_exit_goals_sound:
 assumes "lpp_observer_template_exit_goals gs"
 shows "lpp_observer_exit_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 using assms by (induction gs rule: lpp_observer_template_exit_goals.induct) auto

lemma lpp_observer_template_exit_stack_sound:
 assumes "lpp_observer_template_exit_stack ss"
 shows "\<not>lpp_observer_internal_frame (lpc_return_eval eta ss)"
proof -
 have goals: "\<not>lpp_observer_internal_frame ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),env)#saved)"
  if safe: "lpp_observer_template_exit_goals gs" for gs env saved
  by (rule lpp_observer_exit_goals_frame[OF lpp_observer_template_exit_goals_sound[OF safe]])
 show ?thesis using assms
  apply (induction ss rule: lpp_observer_template_exit_stack.induct)
  subgoal for gs env saved using goals by (simp add: lpc_return_eval_def)
  apply (simp_all add: lpc_return_eval_def lpp_observer_internal_frame_def)
  done
qed

fun lpp_check_observer_univ_exit where
 "lpp_check_observer_univ_exit F ((LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),env)#saved) =
   (f=''2:=..'' \<and> lpp_check_univ_view_domain F a b \<and>
    lpp_observer_template_exit_goals gs \<and> lpp_observer_template_exit_stack saved)"
| "lpp_check_observer_univ_exit F ss = False"

lemma lpp_checked_observer_univ_exit:
 assumes checked: "lpp_check_observer_univ_exit F ss"
 and free: "lpc_free_knowledge (set F) eta"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ss) event result"
 shows "\<not>lpp_observer_internal_frame result"
proof -
 obtain a b gs env saved where shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,b])#gs),env)#saved"
 and domain_check: "lpp_check_univ_view_domain F a b"
 and goals: "lpp_observer_template_exit_goals gs"
 and alternatives: "lpp_observer_template_exit_stack saved"
  using checked by (induction F ss rule: lpp_check_observer_univ_exit.induct) auto
 have domain: "lpp_univ_view_domain (lp_ieval a eta) (lp_ieval b eta)"
  by (rule lpp_check_univ_view_domain_sound[OF domain_check free])
 have exit_goals: "lpp_observer_exit_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  by (rule lpp_observer_template_exit_goals_sound[OF goals])
 have exit_saved: "\<not>lpp_observer_internal_frame (lpc_return_eval eta saved)"
  by (rule lpp_observer_template_exit_stack_sound[OF alternatives])
 show ?thesis
  apply (rule lpp_observer_univ_exit[OF domain exit_goals exit_saved])
  using step by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_observer_univ_exit_unknown_goal_rejected:
 "\<not>lpp_observer_template_exit_goals (LPCAtom (Var x)#gs)"
 by simp

lemma lpp_observer_univ_exit_equality_rejected:
 "\<not>lpp_observer_template_exit_goals (LPCUnify a b#gs)"
 by simp

ML \<open>
val checked = @{thms lpp_observer_template_exit_goals_sound lpp_observer_template_exit_stack_sound
 lpp_checked_observer_univ_exit lpp_observer_univ_exit_unknown_goal_rejected lpp_observer_univ_exit_equality_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted univ exit checker" else ();
\<close>
end
