theory LP_Prolog_Finite_Execution_Step
 imports LP_Prolog_Finite_Continuation_Composition LP_Prolog_Finite_Ground_Binding
begin

text \<open>Lift local finite resolution and equality obligations to the complete
shared answer state. Saved alternatives are retained unchanged or pruned by the
existing rules. Dynamic meta expansion remains an explicit separate obligation.\<close>

lemma lpp_finite_execution_prune:
 "lpp_finite_execution ss \<Longrightarrow> lpp_finite_execution (lpc_answer_prune m ss)"
 using lpc_answer_prune_set_subset[of m ss]
 by (auto simp: lpp_finite_execution_def list_all_iff)

lemma lpp_finite_execution_resolution:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and head: "lpp_finite_term (lp_ieval h rho)"
 and state: "lpp_finite_execution ((LPCClause (LPCAtom a#gs) c m,eta)#es)"
 shows "lpp_finite_execution ((LPCGoals
   (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
    map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),nu)#es)"
proof -
 have call: "lpp_finite_term a" and continuation: "lpp_finite_goals gs"
 and saved: "lpp_finite_execution es"
   using state by (auto simp: lpp_finite_execution_def lpp_finite_goals_def lp_cut_terms.simps)
 show ?thesis using lpp_finite_instance_resolution_finite[OF mgu head call continuation] saved
   by (simp add: lpp_finite_execution_def)
qed

lemma lpp_finite_execution_ground_equality:
 assumes mgu: "lpc_mgu_unify a b gs sigma"
 and ground: "lp_seg_ground b"
 and state: "lpp_finite_execution ((LPCGoals (LPCUnify a b#gs),eta)#es)"
 shows "lpp_finite_execution ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),nu)#es)"
proof -
 have input: "lpp_finite_term a" and continuation: "lpp_finite_goals gs"
 and saved: "lpp_finite_execution es"
   using state by (auto simp: lpp_finite_execution_def lpp_finite_goals_def lp_cut_terms.simps)
 show ?thesis using lpp_ground_equality_mgu_finite_goals[OF mgu input ground continuation] saved
   by (simp add: lpp_finite_execution_def)
qed

lemma lpp_finite_base_answer_step:
 assumes step: "lpc_answer_transition P ss event tt"
 and finite: "lpp_finite_execution ss"
 and heads: "\<And>a gs c m eta es sigma rho.
   ss=(LPCClause (LPCAtom a#gs) c m,eta)#es \<Longrightarrow> c<length P \<Longrightarrow>
   lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
   lpp_finite_term (lp_ieval (fst (P!c)) rho)"
 and equalities: "\<And>a b gs eta es. ss=(LPCGoals (LPCUnify a b#gs),eta)#es \<Longrightarrow> lp_seg_ground b"
 and no_meta: "\<And>a gs eta es. ss=(LPCGoals (LPCMeta a#gs),eta)#es \<Longrightarrow> False"
 shows "lpp_finite_execution tt"
 using step
proof (cases rule: lpc_answer_transition.cases)
 case (resolve c a gs sigma rho m eta es)
 have mgu: "lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) sigma rho" using resolve by simp
 have head: "lpp_finite_term (lp_ieval (fst (P!c)) rho)"
   by (rule heads[OF _ _ mgu]) (use resolve in auto)
 have current: "lpp_finite_execution ((LPCClause (LPCAtom a#gs) c m,eta)#es)"
   using finite resolve by simp
 show ?thesis using lpp_finite_execution_resolution[OF mgu head current] resolve by simp
next
 case (unify a b gs sigma eta es)
 have mgu: "lpc_mgu_unify a b gs sigma" using unify by simp
 have ground: "lp_seg_ground b" by (rule equalities) (use unify in simp)
 have current: "lpp_finite_execution ((LPCGoals (LPCUnify a b#gs),eta)#es)"
   using finite unify by simp
 show ?thesis using lpp_finite_execution_ground_equality[OF mgu ground current] unify by simp
qed (use finite no_meta lpp_finite_execution_prune in
 \<open>auto simp: lpp_finite_execution_def lpp_finite_goals_def lp_cut_terms.simps list_all_iff\<close>)


lemma lpp_finite_execution_scope_goal:
 "lpp_finite_goals (map (lp_cut_scope_goal r) gs)=lpp_finite_goals gs"
proof -
 have terms: "lp_cut_terms (lp_cut_scope_goal r g)=lp_cut_terms g" for g
   by (cases g) (simp_all add: lp_cut_terms.simps)
 show ?thesis by (simp add: lpp_finite_goals_def list_all_iff terms)
qed

lemma lpp_finite_execution_scope:
 "lpp_finite_execution (lpc_return_scope r ss)=lpp_finite_execution ss"
proof -
 have entry: "lpp_finite_execution_entry (lp_cut_scope_entry r e)=lpp_finite_execution_entry e" for e
   by (cases e) (simp_all add: lpp_finite_execution_scope_goal)
 show ?thesis by (simp add: lpp_finite_execution_def list_all_iff entry)
qed

lemma lpp_finite_execution_scope_word:
 "lpp_finite_execution (lpc_return_scope_word swaps ss)=lpp_finite_execution ss"
proof (induct swaps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons pair swaps)
 obtain a b where pair: "pair=(a,b)" by (cases pair) auto
 show ?case by (simp only: pair lpc_return_scope_word.simps Cons.hyps lpp_finite_execution_scope)
qed

ML \<open>
val checked = @{thms lpp_finite_execution_resolution lpp_finite_execution_ground_equality
 lpp_finite_base_answer_step lpp_finite_execution_scope_word};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite execution step" else ();
\<close>
end
