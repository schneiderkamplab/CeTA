theory LP_Prolog_Finite_Reachable_Program
 imports LP_Prolog_Finite_Direct_Program
begin

fun lpp_check_finite_reachable_clause where
 "lpp_check_finite_reachable_clause A (Var x,bs)=False"
| "lpp_check_finite_reachable_clause A (Fun (LPCUser f) ts,bs)=
   ((f,length ts)\<in>A \<longrightarrow> lpp_check_direct_head (Fun (LPCUser f) ts) \<and>
     list_all lpp_direct_source_goal bs \<and> list_all (lpp_static_template A) bs)"
| "lpp_check_finite_reachable_clause A (Fun f ts,bs)=True"

definition lpp_check_finite_reachable_program where
 "lpp_check_finite_reachable_program P A = list_all (lpp_check_finite_reachable_clause A) P"

lemma lpp_finite_reachable_selected:
 assumes checked: "lpp_check_finite_reachable_clause A (h,bs)"
   and selected: "lpp_static_goal A (LPCAtom a)"
   and mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 shows "lpp_check_direct_head h \<and> list_all lpp_direct_source_goal bs \<and>
   list_all (lpp_static_template A) bs"
proof -
 obtain f ts where atom: "a=LPIFun (LPCUser f) ts" and member: "(f,length ts)\<in>A"
   using selected by auto
 have equality: "lp_isubst a sigma=lp_ieval h rho"
   using mgu by (simp add: lpc_mgu_resolve_def)
 show ?thesis using checked equality member
   by (cases h; auto simp: atom split: lp_cut_symbol.splits dest: arg_cong[where f=length])
qed

lemma lpp_finite_reachable_resolve:
 assumes program: "lpp_check_finite_reachable_program P A"
   and index: "c<length P"
   and mgu: "lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) sigma rho"
   and state: "lpp_finite_direct_invariant A ((LPCClause (LPCAtom a#gs) c m,eta)#es)"
 shows "lpp_finite_direct_invariant A ((LPCGoals
   (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
     map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),nu)#es)"
proof -
 have checked: "lpp_check_finite_reachable_clause A (fst (P!c),snd (P!c))"
   using program nth_mem[OF index] by (auto simp: lpp_check_finite_reachable_program_def list_all_iff)
 have selected: "lpp_static_goal A (LPCAtom a)"
   and finite_selected: "lpp_finite_direct_goal (LPCAtom a)"
   and rest: "lpp_finite_direct_goals gs"
   and static_rest: "list_all (lpp_static_goal A) gs"
   and saved: "lpp_finite_direct_invariant A es"
   using state by (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def lpp_static_state_def)
 have clause: "lpp_check_direct_head (fst (P!c))" "list_all lpp_direct_source_goal (snd (P!c))"
   "list_all (lpp_static_template A) (snd (P!c))"
   using lpp_finite_reachable_selected[OF checked selected mgu] by auto
 obtain f H where head: "fst (P!c)=Fun f (map Var H)" and distinct: "distinct H"
   using lpp_check_direct_head_sound[OF clause(1)] by blast
 have terms: "lpp_finite_direct_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
     map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
   using mgu unfolding head
   by (rule lpp_finite_direct_resolution[OF _ finite_selected rest distinct clause(2)])
 show ?thesis using terms saved static_rest clause(3)
   by (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
     lpp_static_state_def list_all_iff intro: lpp_static_evaluate lpp_static_substitute)
qed

lemma lpp_finite_reachable_ordinary_step:
 assumes program: "lpp_check_finite_reachable_program P A"
   and transition: "lpc_answer_transition P ss event tt"
   and state: "lpp_finite_direct_invariant A ss"
 shows "lpp_finite_direct_invariant A tt"
 using transition state
proof (cases rule: lpc_answer_transition.cases)
 case (resolve c a gs sigma rho m eta es)
 then show ?thesis using state lpp_finite_reachable_resolve[where nu="\<lambda>x. lp_isubst (eta x) sigma", OF program]
   by fastforce
next
 case (unify a b gs sigma eta es)
 have finite: "lpp_finite_direct_state tt"
   using state unify lpp_finite_direct_scalar_unify[where nu="\<lambda>x. lp_isubst (eta x) sigma"]
   by (auto simp: lpp_finite_direct_invariant_def)
 show ?thesis using state unify finite
   by (auto simp: lpp_finite_direct_invariant_def lpp_static_state_def list_all_iff intro: lpp_static_substitute)
next
 case (cut m gs eta es)
 have static: "lpp_static_state A (map fst es)"
   using state cut by (auto simp: lpp_finite_direct_invariant_def lpp_static_state_def)
 have pruned: "lpp_static_state A (lp_cut_prune m (map fst es))"
   by (rule lpp_static_prune[OF static])
 show ?thesis using state cut pruned
   by (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
     lpp_static_state_def lpc_answer_prune_erases
     dest: lpp_finite_direct_prune[unfolded lpp_finite_direct_state_def])
qed (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
  lpp_static_state_def list_all_iff lpc_answer_prune_erases
  dest: lpp_finite_direct_prune[unfolded lpp_finite_direct_state_def list_all_iff]
    lpp_static_prune[unfolded lpp_static_state_def list_all_iff])

lemma lpp_finite_reachable_answer_step:
 assumes program: "lpp_check_finite_reachable_program P A"
   and safe: "\<And>f ts result. (f,length ts)\<in>A \<Longrightarrow>
     U f ts result \<Longrightarrow> lpp_finite_direct_outcome result"
   and step: "lpp_answer_transition P B U ss event tt"
   and state: "lpp_finite_direct_invariant A ss"
 shows "lpp_finite_direct_invariant A tt"
 using step state
proof (cases rule: lpp_answer_transition.cases)
 case base
 then show ?thesis using state lpp_finite_reachable_ordinary_step[OF program] by blast
qed (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
      lpp_static_state_def list_all_iff
    dest: safe intro: lpp_finite_direct_substitute lpp_static_substitute)

lemma lpp_finite_reachable_arithmetic_stable:
 assumes program: "lpp_check_finite_reachable_program P A"
   and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
   and step: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain xs ev ys"
   and invariant: "lpp_finite_direct_invariant A xs"
 shows "lpp_finite_direct_invariant A ys"
proof -
 have safe: "lpp_finite_direct_outcome outcome"
   if member: "(f,length ts)\<in>A" and outcome: "lpp_stable_source_builtin operation f ts outcome" for f ts outcome
 proof -
  have selected: "(f,length ts)\<in>lpp_builtin_signature"
    by (rule lpp_finite_source_selected[OF lpp_stable_source_refines_finite[OF outcome]])
  show ?thesis by (rule lpp_direct_arithmetic_outcome[OF signature[OF member selected] outcome])
 qed
 show ?thesis using step invariant lpp_finite_reachable_answer_step[OF program safe]
   by (auto simp: lpp_domain_answers_def)
qed

definition lpp_check_finite_reachable_signature where
 "lpp_check_finite_reachable_signature P signatures =
   (lpp_check_finite_reachable_program P (set signatures) \<and>
    list_all (\<lambda>(f,n). (f,n)\<in>lpp_builtin_signature \<longrightarrow> lpp_direct_arithmetic_name f) signatures)"

lemma lpp_finite_reachable_closed_control_SN:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
   and checked: "lpp_check_finite_direct_control_contexts fuel P Q nds states contexts contexts Fs T returned arity actions"
   and ranked: "lpc_seg_ranked_control rank_of Q"
   and transfer: "lpp_check_transfer_program T SP receipts"
   and source: "lp_cut_source_program P"
   and program: "lpp_check_finite_reachable_signature P signatures"
   and initial: "lpp_finite_direct_invariant (set signatures) ss"
   and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss a"
   and closed: "list_all (\<lambda>x. x\<noteq>None) actions"
 shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) {map fst ss}"
proof -
 have stable: "lpp_finite_direct_invariant (set signatures) ys"
   if "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain xs ev ys"
     "lpp_finite_direct_invariant (set signatures) xs" for xs and ev :: "(nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and ys
   by (rule lpp_finite_reachable_arithmetic_stable[OF _ _ that])
      (use program in \<open>auto simp: lpp_check_finite_reachable_signature_def list_all_iff\<close>)
 have contract: "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ss (UNIV::unit rel) () (\<lambda>_. ())"
   apply (rule lpp_finite_direct_control_contract_contexts[where A="set signatures"])
   apply (fact compatible)
   apply (fact checked)
   apply assumption
   apply (fact ranked)
   apply (fact transfer)
   apply (fact source)
   apply (fact initial)
   apply (fact stable)
   apply (fact represented)
   using closed checked
   apply (auto simp: lpp_check_finite_direct_control_contexts_def list_all_iff; metis nth_mem option.distinct(1))
   by (rule rtrancl_refl)

 show ?thesis by (rule lpp_domain_instrumentation_SN)
   (use contract in \<open>simp add: lp_answer_contract_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_finite_reachable_arithmetic_stable}, @{thm lpp_finite_reachable_closed_control_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite reachable program" else ();
\<close>
end
