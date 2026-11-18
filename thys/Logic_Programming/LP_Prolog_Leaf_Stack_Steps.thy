theory LP_Prolog_Leaf_Stack_Steps
 imports LP_Prolog_Attached_Leaf_Composition LP_Prolog_Normalized_Pair_Leaf
begin

text \<open>Local substitution obligations are lifted over the existing complete
answer transition relation. Saved alternatives retain their own environments;
failure, errors, cut pruning and builtin alternatives are covered explicitly.
This does not discharge the source-specific local substitution obligations.\<close>

definition lpp_leaf_environment_transport where
 "lpp_leaf_environment_transport A specs eta sigma =
   (\<forall>(slot,shape)\<in>set specs. lpp_runtime_leaf_effect A shape (eta slot) \<longrightarrow>
     lpp_runtime_leaf_effect A shape (lp_isubst (eta slot) sigma))"

lemma lpp_answer_prune_subset:
 "set (lpc_answer_prune m ss) \<subseteq> set ss"
 by (induct ss) (auto split: prod.splits lp_cut_entry.splits if_splits)

lemma lpp_leaf_stack_prune:
 "lpp_leaf_stack_invariant A specs ss \<Longrightarrow>
   lpp_leaf_stack_invariant A specs (lpc_answer_prune m ss)"
 by (induct ss) (auto simp: lpp_leaf_stack_invariant_def split: prod.splits lp_cut_entry.splits if_splits)

lemma lpp_leaf_stack_substitution:
 assumes invariant: "lpp_leaf_stack_invariant A specs ((entry,eta)#ss)"
 and local: "lpp_leaf_environment_transport A specs eta sigma"
 shows "lpp_leaf_stack_invariant A specs ((next_entry,\<lambda>x. lp_isubst (eta x) sigma)#ss)"
 by (rule lpp_leaf_stack_active_update[OF invariant])
   (use local in \<open>auto simp: lpp_leaf_environment_transport_def\<close>)

lemma lpp_leaf_stack_base_step:
 assumes step: "lpc_answer_transition P ss event tt"
 and invariant: "lpp_leaf_stack_invariant A specs ss"
 and resolve: "\<And>a gs c m eta es sigma rho.
   ss=(LPCClause (LPCAtom a#gs) c m,eta)#es \<Longrightarrow> c<length P \<Longrightarrow>
   lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
   lpp_leaf_environment_transport A specs eta sigma"
 and unify: "\<And>a b gs eta es sigma.
   ss=(LPCGoals (LPCUnify a b#gs),eta)#es \<Longrightarrow>
   lpc_mgu_unify a b gs sigma \<Longrightarrow>
   lpp_leaf_environment_transport A specs eta sigma"
 shows "lpp_leaf_stack_invariant A specs tt"
 using step invariant resolve unify
 apply (cases rule: lpc_answer_transition.cases)
 apply (auto simp: lpp_leaf_stack_invariant_def lpp_leaf_environment_transport_def list_all_iff
   dest: subsetD[OF lpp_answer_prune_subset])
 apply fastforce+
 done

lemma lpp_leaf_stack_builtin_step:
 assumes step: "lpp_answer_transition P B U ss event tt"
 and invariant: "lpp_leaf_stack_invariant A specs ss"
 and base: "\<And>event tt. lpc_answer_transition P ss event tt \<Longrightarrow>
   lpp_leaf_stack_invariant A specs tt"
 and builtin: "\<And>f ts gs eta es sigma.
   ss=(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es \<Longrightarrow>
   U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
   lpp_leaf_environment_transport A specs eta sigma"
 shows "lpp_leaf_stack_invariant A specs tt"
 using step invariant base builtin
 apply (cases rule: lpp_answer_transition.cases)
 apply (auto simp: lpp_leaf_stack_invariant_def lpp_leaf_environment_transport_def list_all_iff)
 apply fastforce
 done


lemma lpp_leaf_stack_domain_step:
 assumes step: "lpp_domain_answers P B U D ss event tt"
 and invariant: "lpp_leaf_stack_invariant A specs ss"
 and base: "\<And>event tt. lpc_answer_transition P ss event tt \<Longrightarrow>
   lpp_leaf_stack_invariant A specs tt"
 and builtin: "\<And>f ts gs eta es sigma.
   ss=(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es \<Longrightarrow>
   U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
   lpp_leaf_environment_transport A specs eta sigma"
 shows "lpp_leaf_stack_invariant A specs tt"
 using step invariant lpp_leaf_stack_builtin_step[OF _ invariant base builtin]
 by (auto simp: lpp_domain_answers_def)

lemma lpp_leaf_environment_arithmetic:
 assumes success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess sigma)"
 and atoms: "\<And>f. Fun (LPCUser f) []\<in>A"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u={}"
 shows "lpp_leaf_environment_transport A specs eta sigma"
 unfolding lpp_leaf_environment_transport_def
 by (auto intro: lpp_runtime_leaf_effect_arithmetic[OF _ success atoms ground])

lemma lpp_leaf_environment_matching:
 fixes eta sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu=lp_ieval call eta"
 and covered: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   slot\<in>vars_term call \<union> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_environment_transport A specs eta sigma"
 unfolding lpp_leaf_environment_transport_def
 by (auto intro: lpp_runtime_leaf_effect_matching[OF _ mgu matching covered])


lemma lpp_leaf_environment_ground_binding:
 fixes sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify (LPIVar x) (lp_ieval u LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) sigma"
 and ground: "\<And>t. t\<in>A \<Longrightarrow> vars_term t={}"
 and allowed: "u\<in>A"
 and covered: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   set2_lp_iterm (eta slot) \<subseteq> insert x
    (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_environment_transport A specs eta sigma"
 unfolding lpp_leaf_environment_transport_def
 by (auto intro: lpp_runtime_leaf_effect_ground_binding[OF _ mgu ground allowed covered])

lemma lpp_leaf_environment_reflexive:
 fixes eta sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and equal: "lp_ieval a eta=lp_ieval b eta"
 and covered: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   slot\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_environment_transport A specs eta sigma"
 unfolding lpp_leaf_environment_transport_def
 by (auto intro: lpp_runtime_leaf_effect_reflexive[OF _ mgu equal covered])

ML \<open>
val checked = @{thms lpp_answer_prune_subset lpp_leaf_stack_prune lpp_leaf_stack_substitution lpp_leaf_stack_base_step lpp_leaf_stack_builtin_step
 lpp_leaf_stack_domain_step lpp_leaf_environment_arithmetic lpp_leaf_environment_matching
 lpp_leaf_environment_ground_binding lpp_leaf_environment_reflexive};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf stack steps" else ();
\<close>
end
