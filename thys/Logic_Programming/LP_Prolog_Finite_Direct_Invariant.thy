theory LP_Prolog_Finite_Direct_Invariant
 imports LP_Prolog_Finite_Direct_Builtins LP_Prolog_Builtin_Domain
   LP_Answer_Invariant_Refinement
begin

definition lpp_finite_direct_invariant where
 "lpp_finite_direct_invariant A ss =
   (lpp_finite_direct_state ss \<and> lpp_static_state A (map fst ss))"

lemma lpp_finite_direct_answer_step:
 assumes program: "lpp_finite_direct_program P" "lpp_static_program A P"
   and safe: "\<And>f ts result. (f,length ts)\<in>A \<Longrightarrow>
     U f ts result \<Longrightarrow> lpp_finite_direct_outcome result"
   and step: "lpp_answer_transition P B U ss event tt"
   and state: "lpp_finite_direct_invariant A ss"
 shows "lpp_finite_direct_invariant A tt"
 using step state
proof (cases rule: lpp_answer_transition.cases)
 case base
 then show ?thesis using state program lpp_finite_direct_ordinary_step
   lpp_static_mgu_preserved lpc_answer_transition_erases
   by (metis lpp_finite_direct_invariant_def)
qed (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
      lpp_static_state_def list_all_iff
    dest: safe
    intro: lpp_finite_direct_substitute lpp_static_substitute)

lemma lpp_finite_direct_domain_step:
 assumes "lpp_finite_direct_program P" "lpp_static_program A P"
   "\<And>f ts result. (f,length ts)\<in>A \<Longrightarrow>
     U f ts result \<Longrightarrow> lpp_finite_direct_outcome result"
   "lpp_domain_answers P B U D ss event tt"
   "lpp_finite_direct_invariant A ss"
 shows "lpp_finite_direct_invariant A tt"
 using assms(4,5) lpp_finite_direct_answer_step[OF assms(1,2,3)]
 by (auto simp: lpp_domain_answers_def)

lemma lpp_finite_direct_initial:
 assumes "(f,length ts)\<in>A"
 shows "lpp_finite_direct_invariant A
   [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) LPIVar)],eta)]"
 using assms lpp_finite_term_initial[of "Fun (LPCUser f) ts"]
 by (simp add: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
   lpp_static_state_def)

lemma lpp_finite_direct_contract_refinement:
 assumes initial: "lpp_finite_direct_invariant A ss"
   and program: "lpp_finite_direct_program P" "lpp_static_program A P"
   and safe: "\<And>f ts result. (f,length ts)\<in>A \<Longrightarrow>
     U f ts result \<Longrightarrow> lpp_finite_direct_outcome result"
   and refines: "\<And>xs event ys. lpp_finite_direct_invariant A xs \<Longrightarrow>
     lpp_domain_answers P B U D xs event ys \<Longrightarrow> V xs event ys"
   and contract: "lp_answer_contract V ss R t ret"
 shows "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
 by (rule lp_answer_contract_invariant_refinement[where I="lpp_finite_direct_invariant A" and T="lpp_domain_answers P B U D" and U=V, OF initial _ refines contract])
    (rule lpp_finite_direct_domain_step[OF program safe]; assumption)

lemma lpp_finite_direct_is_normalization:
 assumes "lpp_finite_direct_invariant A
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#es)"
 shows "lpp_finite_direct_invariant A
   ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#es)"
 using assms by (auto simp: lpp_finite_direct_invariant_def
   lpp_finite_direct_state_def lpp_static_state_def)

ML \<open>
val checked = [@{thm lpp_finite_direct_domain_step},
 @{thm lpp_finite_direct_initial}, @{thm lpp_finite_direct_is_normalization}, @{thm lpp_finite_direct_contract_refinement}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite direct invariant" else ();
\<close>
end
