theory LP_Prolog_Attached_Leaf_Composition
 imports LP_Prolog_Runtime_Leaf_Invariant LP_Prolog_Actual_Call_Composition
begin

text \<open>Caller leaf contracts belong to actual attached execution. A standalone
prefix may overapproximate unobserved caller variables. The shared invariant
composition theorem retains the dormant continuation in every checked step.\<close>

definition lpp_leaf_stack_invariant where
 "lpp_leaf_stack_invariant A specs ss = list_all
   (\<lambda>frame. list_all (\<lambda>(slot,shape). lpp_runtime_leaf_effect A shape (snd frame slot)) specs) ss"

lemma lpp_leaf_stack_tail:
 "lpp_leaf_stack_invariant A specs (frame#ss) \<Longrightarrow> lpp_leaf_stack_invariant A specs ss"
 by (simp add: lpp_leaf_stack_invariant_def)

lemma lpp_leaf_stack_head:
 assumes invariant: "lpp_leaf_stack_invariant A specs ((source_frame,eta)#ss)"
 and member: "(slot,shape)\<in>set specs"
 shows "lpp_runtime_leaf_effect A shape (eta slot)"
 using assms by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)

lemma lpp_leaf_stack_active_update:
 assumes invariant: "lpp_leaf_stack_invariant A specs ((source_frame,eta)#ss)"
 and active: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   lpp_runtime_leaf_effect A shape (eta slot) \<Longrightarrow> lpp_runtime_leaf_effect A shape (rho slot)"
 shows "lpp_leaf_stack_invariant A specs ((next_entry,rho)#ss)"
 using invariant active by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)

lemma lpp_attached_leaf_call_composition:
 assumes program: "lp_cut_source_program P"
 and prefix: "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {ss}"
 and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
 and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
 and initial: "I ss"
 and preserve: "\<And>us ev vs. I us \<Longrightarrow>
   (ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>* \<Longrightarrow>
   lpc_prefix_active us \<Longrightarrow>
   lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow> I vs"
 and tail: "\<And>eta vs. I ((LPCGoals [],eta)#vs) \<Longrightarrow> I vs"
 and continuation: "\<And>eta vs. lp_actual_answer (lpp_domain_answers P B U D) ss eta \<Longrightarrow>
   I ((LPCGoals [],eta)#vs) \<Longrightarrow>
   SN_on (lp_answer_steps (lpp_domain_answers P B U D))
    {[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)]}"
 shows "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {lpc_attach_answers rest ss}"
proof -
 have prefix_contract: "lp_answer_contract (lpp_domain_answers P B U D) ss {} () (\<lambda>_. ())"
  using prefix by (simp add: lp_constant_answer_contract)
 have composed: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest ss) {} () (\<lambda>_. ())"
 proof (rule lpp_domain_contract_compose_actual_invariant[where I=I and rest=rest,
   OF program prefix_contract valid separated initial preserve tail])
  fix eta vs
  assume actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
   and invariant: "I ((LPCGoals [],eta)#vs)"
  show "lp_answer_contract (lpp_domain_answers P B U D)
   [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] {} () (\<lambda>_. ())"
   using continuation[OF actual invariant] by (simp add: lp_constant_answer_contract)
 qed
 show ?thesis using composed by (simp add: lp_constant_answer_contract)
qed


lemma lpp_leaf_stack_rejects_stale_saved:
 assumes member: "(slot,shape)\<in>set specs"
 and stale: "\<not>lpp_runtime_leaf_effect A shape (saved_env slot)"
 shows "\<not>lpp_leaf_stack_invariant A specs ((active_frame,active_env)#(saved_frame,saved_env)#ss)"
 using member stale by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)

lemma lpp_isolated_prefix_unobserved_return:
 fixes x y f g :: string
 assumes distinct: "x\<noteq>y" "f\<noteq>g"
 defines "sigma \<equiv> LPIVar(x:=LPIFun (LPCUser f) [],y:=LPIFun (LPCUser g) [])"
 shows "lp_actual_answer (lpc_answer_transition [])
   [(LPCGoals [LPCUnify (LPIVar x) (LPIFun (LPCUser f) [])],LPIVar)] sigma \<and>
   \<not>lpp_bounded_images {Fun (LPCUser f) []} sigma {y}"
proof -
 have mgu: "lpc_mgu_unify (LPIVar x) (LPIFun (LPCUser f) []) [] sigma"
 and unbounded: "\<not>lpp_bounded_images {Fun (LPCUser f) []} sigma {y}"
  using lpp_unobserved_binding_not_bounded[OF distinct(1), of "LPCUser f" "LPCUser g"]
   distinct(2) unfolding sigma_def by auto
 have step: "lpc_answer_transition []
   [(LPCGoals [LPCUnify (LPIVar x) (LPIFun (LPCUser f) [])],LPIVar)] None [(LPCGoals [],sigma)]"
  using lpc_answer_transition.unify[OF mgu, where P = "[]" and \<eta> = LPIVar and es = "[]"] by simp
 have reached: "([(LPCGoals [LPCUnify (LPIVar x) (LPIFun (LPCUser f) [])],LPIVar)],
   [(LPCGoals [],sigma)])\<in>(lp_answer_steps (lpc_answer_transition []))\<^sup>*"
  by (rule r_into_rtrancl) (use step in \<open>auto simp: lp_answer_steps_def\<close>)
 have actual: "lp_actual_answer (lpc_answer_transition [])
   [(LPCGoals [LPCUnify (LPIVar x) (LPIFun (LPCUser f) [])],LPIVar)] sigma"
  using reached lpc_answer_transition.success[where P = "[]" and \<eta> = sigma and es = "[]"]
  unfolding lp_actual_answer_def by blast
 show ?thesis using actual unbounded by blast
qed

ML \<open>
val checked = @{thms lpp_leaf_stack_tail lpp_leaf_stack_head lpp_leaf_stack_active_update
 lpp_attached_leaf_call_composition lpp_leaf_stack_rejects_stale_saved
 lpp_isolated_prefix_unobserved_return};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached leaf composition" else ();
\<close>
end
