theory LP_Prolog_Leaf_Univ_Check
 imports LP_Prolog_Leaf_Ordinary_Check LP_Prolog_Separation_Univ_Check
begin

theorem lpp_checked_leaf_separation_univ_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
   (LPPFUniv value_var name_var args_var middle facts)"
 and extra: "lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof -
 obtain a gs active saved where
  shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,Fun pair_symbol [output_name,output_args]])#gs),active)#saved"
  and incoming: "set [LPPSeparate a output_name,LPPSeparate a output_args]\<subseteq> set (separation_contexts!i)"
  and bound: "lpcl_target middle<length separation_contexts"
  and transport: "lpp_check_separation_transport
    [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]
    (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
  using lpp_checked_separation_univ_shape[OF extra] by blast
 show ?thesis by (rule lpp_leaf_univ_separation_node_contract[OF compatible transfer checked shape incoming bound transport])
qed

lemma lpp_leaf_univ_missing_context_rejected:
 "\<not> lpp_check_separation_univ [] i ss name_var args_var middle pair_symbol output_name output_args"
 by simp

lemma lpp_leaf_univ_missing_middle_rejected:
 "length separation_contexts \<le> lpcl_target middle \<Longrightarrow>
  \<not> lpp_check_separation_univ separation_contexts i ss name_var args_var middle pair_symbol output_name output_args"
 by simp

lemma lpp_leaf_ordinary_is_missing_middle_rejected:
 "\<not> lpp_empty_separation_target separation_contexts middle \<Longrightarrow>
  \<not> lpp_check_separation_ordinary separation_contexts ss (LPPFIs result_var middle facts)"
 by (auto split: list.splits prod.splits lp_cut_entry.splits lp_cut_goal.splits term.splits lp_cut_symbol.splits)

ML \<open>
val checked = @{thms lpp_checked_leaf_separation_univ_node_contract lpp_leaf_univ_missing_context_rejected
 lpp_leaf_univ_missing_middle_rejected lpp_leaf_ordinary_is_missing_middle_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted leaf separation univ checker" else ();
\<close>
end
