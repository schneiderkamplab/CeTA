theory LP_Prolog_Observer_Univ_Exit
 imports LP_Prolog_Observer_Frontier_Shapes
begin

fun lpp_observer_exit_goals where
 "lpp_observer_exit_goals [] = True"
| "lpp_observer_exit_goals (LPCUnify a b#gs) = False"
| "lpp_observer_exit_goals (LPCAtom (LPIVar x)#gs) = False"
| "lpp_observer_exit_goals (LPCAtom (LPIFun (LPCUser f) ts)#gs) = (f\<noteq>''2:=..'')"
| "lpp_observer_exit_goals gs = True"

lemma lpp_observer_exit_goals_subst:
 "lpp_observer_exit_goals gs \<Longrightarrow> lpp_observer_exit_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
 by (induction gs rule: lpp_observer_exit_goals.induct) auto

lemma lpp_observer_exit_goals_frame:
 "lpp_observer_exit_goals gs \<Longrightarrow> \<not>lpp_observer_internal_frame ((LPCGoals gs,env)#saved)"
 by (induction gs rule: lpp_observer_exit_goals.induct)
  (auto simp: lpp_observer_internal_frame_def elim: lpp_observer_univ_frame.elims)

lemma lpp_observer_equality_exit:
 assumes goals: "lpp_observer_exit_goals gs"
 and alternatives: "\<not>lpp_observer_internal_frame saved"
 and step: "lpc_answer_transition P ((LPCGoals (LPCUnify a b#gs),env)#saved) event result"
 shows "\<not>lpp_observer_internal_frame result"
proof -
 have success: "\<not>lpp_observer_internal_frame ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),ret)#saved)" for sigma ret
  by (rule lpp_observer_exit_goals_frame[OF lpp_observer_exit_goals_subst[OF goals]])
 show ?thesis using step by (cases rule: lpc_answer_transition.cases) (auto simp: alternatives success)
qed

lemma lpp_observer_univ_exit:
 assumes domain: "lpp_univ_view_domain input_value requested"
 and goals: "lpp_observer_exit_goals gs"
 and alternatives: "\<not>lpp_observer_internal_frame saved"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [input_value,requested])#gs),env)#saved) event result"
 shows "\<not>lpp_observer_internal_frame result"
proof -
 have path: "result=[] \<or> (\<exists>f ts. lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#gs),env)#saved) None result)"
  using lpp_observer_univ_actual_normalized_path[OF domain step] by blast
 show ?thesis using path lpp_observer_equality_exit[OF goals alternatives]
  by (auto simp: lpp_observer_internal_frame_def)
qed

ML \<open>
val checked = @{thms lpp_observer_exit_goals_subst lpp_observer_exit_goals_frame lpp_observer_equality_exit lpp_observer_univ_exit};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted actual univ exits" else ();
\<close>
end
