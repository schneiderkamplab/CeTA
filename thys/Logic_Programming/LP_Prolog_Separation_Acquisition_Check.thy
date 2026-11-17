theory LP_Prolog_Separation_Acquisition_Check
 imports LP_Prolog_Separation_Pair_Check LP_Prolog_Separation_Reflexive_Contract
   LP_Prolog_Separation_Normalized_Fresh
begin

text \<open>The logical fresh-clause predicate uses an existential list tail.
An equivalent pattern equation makes its existing check executable.\<close>

declare lpp_check_fresh_univ_clause_def[code del]

lemma lpp_check_fresh_univ_clause_code[code]:
 "lpp_check_fresh_univ_clause h bs input_variable name_variable arguments_variable =
  (lpp_check_fresh_decomposition h bs input_variable name_variable arguments_variable \<and>
   (case bs of [] \<Rightarrow> False | front_goal#tail_goals \<Rightarrow>
    front_goal=LPCAtom (Fun (LPCUser ''2:=..'') [Var input_variable,
      Fun (LPCUser ''2:prolog_data_2e'') [Var name_variable,Var arguments_variable]])))"
 by (cases bs) (auto simp: lpp_check_fresh_univ_clause_def)

definition lpp_check_separation_reflexive where
 "lpp_check_separation_reflexive nd ctx separation_contexts i a b gs k l mode yes no retained no_separation =
  ((i<length separation_contexts) \<and>
   (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
   lpcl_target yes<length separation_contexts \<and>
   lpp_check_separation_transport (map (\<lambda>observation. lpp_separation_subst observation (lp_cut_refresh k (set (lpcn_ground nd)))) retained) (separation_contexts!lpcl_target yes)
     (lp_cut_instance_subst (lpcl_bindings yes))) \<and>
   (mode\<noteq>LPCAlwaysSuccess \<longrightarrow>
   lpcl_target no<length separation_contexts \<and>
   lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
     (lp_cut_instance_subst (lpcl_bindings no))) \<and>
   (lpp_check_equation_rewrite ctx a b) \<and>
   (lpp_check_reflexive_separation k retained gs) \<and>
   (set retained\<subseteq> set (separation_contexts!i)) \<and>
   (set no_separation\<subseteq> set (separation_contexts!i)) \<and>
   (2 * k \<le> l))"

theorem lpp_checked_separation_reflexive_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and extra: "lpp_check_separation_reflexive (nds!i) (contexts!i) separation_contexts i a b gs k l mode yes no retained no_separation"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
 apply (rule lpp_reflexive_separation_node_contract[OF compatible transfer checked shape])
 using extra by (auto simp: lpp_check_separation_reflexive_def)

definition lpp_check_separation_fresh where
 "lpp_check_separation_fresh fuel P nd separation_contexts i a c k l mode yes no normalized_facts no_separation x y z match_bindings =
  ((c<length P) \<and>
   (i<length separation_contexts) \<and>
   (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
   lpcl_target yes<length separation_contexts \<and>
   lpp_check_separation_transport normalized_facts (separation_contexts!lpcl_target yes)
     (lp_cut_instance_subst (lpcl_bindings yes))) \<and>
   (mode\<noteq>LPCAlwaysSuccess \<longrightarrow>
   lpcl_target no<length separation_contexts \<and>
   lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
     (lp_cut_instance_subst (lpcl_bindings no))) \<and>
   (lpp_check_separation_normalize fuel
   (lp_cut_resolution_equations k l (lpcn_ground nd) a (fst (P!c)))
   (map (\<lambda>observation. lpp_separation_subst observation (\<lambda>v. Var (lp_prefix l v)))
     [LPPSeparate (Var x) (Var y),LPPSeparate (Var x) (Var z)]) normalized_facts) \<and>
   (2 * k \<le> l) \<and>
   (\<forall>v\<in>vars_term a. length v<k) \<and>
   (lp_cut_check_match a (fst (P!c)) match_bindings) \<and>
   (lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z) \<and>
   (set no_separation\<subseteq> set (separation_contexts!i)))"

theorem lpp_checked_separation_fresh_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and extra: "lpp_check_separation_fresh fuel P (nds!i) separation_contexts i a c k l mode yes no normalized_facts no_separation x y z match_bindings"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
 apply (rule lpp_normalized_fresh_matching_separation_node_contract[OF compatible transfer checked shape])
 using extra by (auto simp: lpp_check_separation_fresh_def)

ML \<open>
val checked = @{thms lpp_check_fresh_univ_clause_code lpp_checked_separation_reflexive_node_contract lpp_checked_separation_fresh_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation acquisition checks" else ();
\<close>
end
