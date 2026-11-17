theory LP_Prolog_Separation_Univ_Check
 imports LP_Prolog_Separation_Acquisition_Check LP_Prolog_Univ_Separation_Node
begin

fun lpp_check_separation_univ where
 "lpp_check_separation_univ separation_contexts i ss name_var args_var middle pair_symbol output_name output_args =
  (i<length separation_contexts \<and> lpcl_target middle<length separation_contexts \<and>
   (case ss of (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved \<Rightarrow>
    f=''2:=..'' \<and> length ts=2 \<and> ts!1=Fun pair_symbol [output_name,output_args] \<and>
    set [LPPSeparate (ts!0) output_name,LPPSeparate (ts!0) output_args]\<subseteq> set (separation_contexts!i) \<and>
    lpp_check_separation_transport
      [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]
      (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))
   | _ \<Rightarrow> False))"

lemma lpp_checked_separation_univ_shape:
 assumes "lpp_check_separation_univ separation_contexts i ss name_var args_var middle pair_symbol output_name output_args"
 obtains a gs active saved where
  "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,Fun pair_symbol [output_name,output_args]])#gs),active)#saved"
  "set [LPPSeparate a output_name,LPPSeparate a output_args]\<subseteq> set (separation_contexts!i)"
  "lpcl_target middle<length separation_contexts"
  "lpp_check_separation_transport
    [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]
    (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
 using assms by (auto simp: length_Suc_conv numeral_2_eq_2
   split!: list.splits prod.splits lp_cut_entry.splits lp_cut_goal.splits term.splits lp_cut_symbol.splits)

theorem lpp_checked_separation_univ_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
   (LPPFUniv value_var name_var args_var middle facts)"
 and extra: "lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
proof -
 obtain a gs active saved where
  shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,Fun pair_symbol [output_name,output_args]])#gs),active)#saved"
  and incoming: "set [LPPSeparate a output_name,LPPSeparate a output_args]\<subseteq> set (separation_contexts!i)"
  and bound: "lpcl_target middle<length separation_contexts"
  and transport: "lpp_check_separation_transport
    [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]
    (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
  using lpp_checked_separation_univ_shape[OF extra] by blast
 show ?thesis by (rule lpp_finite_univ_separation_node_contract[OF compatible transfer checked shape incoming bound transport])
qed

ML \<open>
val checked = @{thms lpp_checked_separation_univ_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation univ checker" else ();
\<close>
end
