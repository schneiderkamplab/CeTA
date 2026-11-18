theory LP_Prolog_Leaf_Head_Check
 imports LP_Prolog_Leaf_Univ_Check
begin

theorem lpp_checked_leaf_separation_head_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors resolution_bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and head: "lpp_check_separation_head P (nds!i) (contexts!i) a c witness"
 and coverage: "lpp_check_relational_leaf_coverage (functor_contexts!i) (map fst specs) active a gs"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts)
   (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof (cases witness)
 case (LPPSMatching bindings)
 have matching: "lp_cut_check_match a (fst (P!c)) bindings" using head LPPSMatching by simp
 show ?thesis by (rule lpp_relational_leaf_empty_separation_matching_node_contract[OF compatible transfer checked shape matching coverage success_target failure_target])
next
 case (LPPSAnchored f actuals hs G)
 have call: "a=Fun f actuals" and source_head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs" and anchored: "lpp_check_anchored_head G actuals hs"
 and ground: "set G\<subseteq> set (lpcn_ground (nds!i))\<union>lpp_source_context_ground (contexts!i)"
  using head LPPSAnchored by auto
 show ?thesis by (rule lpp_relational_leaf_empty_separation_anchored_node_contract[OF compatible transfer checked[unfolded call]
   shape[unfolded call] source_head lengths anchored ground coverage[unfolded call] success_target failure_target])
next
 case (LPPSSpine f arg actuals x y H)
 have call: "a=Fun f (arg#actuals)"
 and source_head: "fst (P!c)=Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and distinct: "distinct (x#y#H)" and lengths: "length H=length actuals"
 and spine: "LPPOShape lpp_spine_grammar (LPReturnShape 0) arg\<in>set (snd (snd (contexts!i)))"
  using head LPPSSpine by auto
 show ?thesis by (rule lpp_relational_leaf_empty_separation_spine_node_contract[OF compatible transfer checked[unfolded call]
   shape[unfolded call] source_head distinct lengths spine coverage[unfolded call] success_target failure_target])
qed

ML \<open>
val checked = @{thms lpp_checked_leaf_separation_head_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf head checker" else ();
\<close>
end
