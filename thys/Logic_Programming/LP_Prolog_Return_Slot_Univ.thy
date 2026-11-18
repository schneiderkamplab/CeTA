theory LP_Prolog_Return_Slot_Univ
 imports LP_Prolog_Return_Slot_Reindex LP_Cut_MGU_Continuation_Subset
begin

lemma lpp_normalized_univ_preserves_return_slot:
 fixes eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and tau :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
     (lpp_argument_list (LPIFun (names f) []#ts))#
      map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and second: "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs) tau"
 and known: "lpp_runtime_leaf_effect A initial_structure (eta v)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "{x,y}\<inter>set2_lp_iterm (eta v)={}"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst (lp_isubst (eta v) sigma) tau)"
proof -
 let ?eta = "\<lambda>name. eta (length name)"
 let ?gs = "lpp_named_return_goals gs"
 have mapped_second: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?eta) sigma)) ?gs =
   map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs"
  using lpp_named_return_goals_eval[of "\<lambda>n. lp_isubst (eta n) sigma" gs]
  by (simp add: lp_ieval_subst)
 have occurrence: "lpp_return_slot_name v\<in>(\<Union>g\<in>set ?gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using covered by (simp add: lpp_named_return_goals_support)
 have effect: "lpp_runtime_leaf_effect A initial_structure
   (lp_isubst (lp_isubst (?eta (lpp_return_slot_name v)) sigma) tau)"
 proof (rule lpp_normalized_univ_preserves_caller_leaf[where eta="?eta" and gs="?gs",
   OF _ _ _ finite distinct fresh _ occurrence])
  show "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
     (lpp_argument_list (LPIFun (names f) []#ts))#
      map (lp_cut_map (\<lambda>t. lp_ieval t ?eta)) ?gs) sigma"
   using first by (simp add: lpp_named_return_goals_eval)
  show "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?eta) sigma)) ?gs) tau"
   using second by (simp only: mapped_second)
  show "lpp_runtime_leaf_effect A initial_structure (?eta (lpp_return_slot_name v))"
   using known by simp
  show "{x,y}\<inter>set2_lp_iterm (?eta (lpp_return_slot_name v))={}"
   using protected by simp
 qed
 show ?thesis using effect by simp
qed

lemma lpp_attached_normalized_univ_preserves_return_slot:
 fixes eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and tau :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
     (lpp_argument_list (LPIFun (names f) []#ts))#
      (pending_goals @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)) sigma"
 and second: "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) pending_goals @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs) tau"
 and known: "lpp_runtime_leaf_effect A initial_structure (eta v)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "{x,y}\<inter>set2_lp_iterm (eta v)={}"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst (lp_isubst (eta v) sigma) tau)"
proof (rule lpp_normalized_univ_preserves_return_slot[where eta=eta and v=v and gs=gs and sigma=sigma and tau=tau,
 OF _ _ known finite distinct fresh protected covered])
 show "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
     (lpp_argument_list (LPIFun (names f) []#ts))#
      map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
  by (rule lpc_mgu_unify_continuation_subset[OF first]) auto
 show "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs) tau"
  by (rule lpc_mgu_unify_continuation_subset[OF second]) auto
qed

lemma lpp_attached_normalized_univ_leaf_stack:
 fixes eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and tau :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
     (lpp_argument_list (LPIFun (names f) []#ts))#
      (pending_goals @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)) sigma"
 and second: "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) pending_goals @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs) tau"
 and invariant: "lpp_leaf_stack_invariant A specs ((entry,eta)#saved)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow> {x,y}\<inter>set2_lp_iterm (eta slot)={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) gs"
 shows "lpp_leaf_stack_invariant A specs ((next_entry,\<lambda>slot. lp_isubst (lp_isubst (eta slot) sigma) tau)#saved)"
proof (rule lpp_leaf_stack_active_update[OF invariant])
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect A shape (eta slot)"
 have live: "slot\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using lpp_check_attached_leaf_slots_sound[OF covered] member by force
 show "lpp_runtime_leaf_effect A shape (lp_isubst (lp_isubst (eta slot) sigma) tau)"
  by (rule lpp_attached_normalized_univ_preserves_return_slot[where eta=eta and v=slot and gs=gs and pending_goals=pending_goals and sigma=sigma and tau=tau
    and names=names and f=f and ts=ts and x=x and y=y and A=A and initial_structure=shape, OF first second known finite distinct fresh protected[OF member] live])
qed

ML \<open>
val checked = @{thms lpp_normalized_univ_preserves_return_slot lpp_attached_normalized_univ_preserves_return_slot lpp_attached_normalized_univ_leaf_stack};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted return-slot univ transport" else ();
\<close>
end
