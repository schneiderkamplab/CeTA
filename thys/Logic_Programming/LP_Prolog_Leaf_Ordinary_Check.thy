theory LP_Prolog_Leaf_Ordinary_Check
 imports LP_Prolog_Leaf_Builtin_Contracts
begin

theorem lpp_leaf_separation_ordinary_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity action"
 and extra: "lpp_check_separation_ordinary separation_contexts (states!i) action"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof (cases action)
 case (LPPFCut control fs ns)
 show ?thesis
 proof (cases control)
  case LPCRTerminal
  have "states!i=[]" using extra LPPFCut LPCRTerminal by simp
  then show ?thesis by (rule lpp_exhausted_premised_functor_node_contract)
 next
  case LPCRInconsistent
  have inconsistent: "lp_cut_check_inconsistent (lpcn_guards (nds!i))"
   using checked LPPFCut LPCRInconsistent by (simp add: lpp_check_functor_source_action_def)
  show ?thesis unfolding lpp_premised_functor_node_contract_def
   using lp_cut_checked_inconsistent[OF inconsistent] by blast
 next
  case (LPCRAdmin event successor e)
  have clear: "lpp_no_builtin_frame (states!i)"
   and check: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity event successor e"
   using checked LPPFCut LPCRAdmin by (auto simp: lpp_check_functor_source_action_def)
  have simple: "lpp_simple_control_frame (states!i)"
   and bound: "lpcl_target e<length separation_contexts"
   and empty: "separation_contexts!lpcl_target e=[]"
   using extra LPPFCut LPCRAdmin by (auto simp: lpp_empty_separation_target_def)
  show ?thesis by (rule lpp_leaf_separation_admin_node_contract[OF compatible transfer check simple clear bound empty])
 next
  case (LPCRCase m f ts gs active saved e)
  have clear: "lpp_no_builtin_frame (states!i)"
   and shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved"
   and check: "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (contexts!i) (functor_contexts!i) m f ts gs active saved e"
   using checked LPPFCut LPCRCase by (auto simp: lpp_check_functor_source_action_def)
  have simple: "lpp_simple_control_frame (states!i)"
   and bound: "lpcl_target e<length separation_contexts"
   and empty: "separation_contexts!lpcl_target e=[]"
   using extra LPPFCut LPCRCase by (auto simp: lpp_empty_separation_target_def)
  show ?thesis by (rule lpp_leaf_separation_case_node_contract[OF compatible transfer check shape simple clear bound empty])
 next
  case LPCRMeta then show ?thesis using extra LPPFCut by simp
 next
  case LPCREquality then show ?thesis using extra LPPFCut by simp
 next
  case LPCRResolution then show ?thesis using extra LPPFCut by simp
 qed
next
 case (LPPFTest yes no fs ns)
 obtain f a gs active saved where
   shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
   and yes: "lpp_empty_separation_target separation_contexts yes"
   and no: "lpp_empty_separation_target separation_contexts no"
  using lpp_separation_ordinary_test_shape[OF extra[unfolded LPPFTest]] by blast
 show ?thesis
  apply (rule lpp_leaf_separation_test_node_contract[OF compatible transfer checked[unfolded LPPFTest] shape])
  using yes no by (auto simp: lpp_empty_separation_target_def)
next
 case (LPPFIs r middle fs)
 obtain a e gs active saved where
   shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
   and target: "lpp_empty_separation_target separation_contexts middle"
  using lpp_separation_ordinary_is_shape[OF extra[unfolded LPPFIs]] by blast
 show ?thesis
  apply (rule lpp_leaf_separation_is_node_contract[OF compatible transfer checked[unfolded LPPFIs] shape])
  using target by (auto simp: lpp_empty_separation_target_def)
next
 case LPPFUniv then show ?thesis using extra by simp
next
 case (LPPFTrim successor barriers e fs)
 show ?thesis
  apply (rule lpp_leaf_separation_trim_node_contract[OF compatible transfer checked[unfolded LPPFTrim]])
  using extra LPPFTrim by (auto simp: lpp_empty_separation_target_def)
next
 case (LPPFParallel links factss)
 show ?thesis
  apply (rule lpp_leaf_separation_parallel_node_contract[OF compatible transfer checked[unfolded LPPFParallel]])
  using extra LPPFParallel by (auto simp: lpp_empty_separation_target_def list_all_iff)
qed

ML \<open>
val checked = @{thms lpp_leaf_separation_ordinary_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted leaf ordinary checker" else ();
\<close>
end
