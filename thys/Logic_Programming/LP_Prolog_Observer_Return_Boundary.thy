theory LP_Prolog_Observer_Return_Boundary
 imports LP_Prolog_Observer_Invariant LP_Prolog_Observer_Boundary_Contracts
begin

text \<open>A successful helper return activates the caller continuation. The
helper's administrative return edge cannot discharge that continuation. Caller
leaf facts are obtained from the actual joint state, never from helper termination.\<close>

lemma lpp_observer_single_return_contract:
 assumes shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=[(LPCGoals [],helper_env)]"
 and invariant: "lpp_observer_invariant A specs rest runtime"
 and continuation: "\<And>rho. list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
proof -
 obtain env where runtime: "runtime=[(LPCGoals [],env)]"
  using shape by (auto simp: lpc_reinterface_def map_eq_Cons_conv)
 let ?rho = "\<lambda>x. env (Inr x)"
 have exact: "lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)=
   [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x ?rho)) rest),?rho)]"
  by (simp add: runtime lpc_reinterface_def lpc_attach_answers_def)
 have leaf: "list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (?rho slot)) specs"
  using invariant by (simp add: runtime lpp_observer_invariant_def lpc_reinterface_def lpp_leaf_stack_invariant_def)
 have finite: "lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x ?rho)) rest),?rho)]"
  using invariant exact by (simp add: lpp_observer_invariant_def)
 show ?thesis unfolding exact by (rule continuation[OF leaf finite])
qed

lemma lpp_observer_single_return_joint_contract:
 assumes shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=[(LPCGoals [],helper_env)]"
 and invariant: "lpp_observer_invariant A specs rest runtime"
 and continuation: "\<And>env. (\<lambda>x. env (Inl x))=helper_env \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (env (Inr slot))) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x (\<lambda>i. env (Inr i)))) rest),\<lambda>i. env (Inr i))] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x (\<lambda>i. env (Inr i)))) rest),\<lambda>i. env (Inr i))] R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
proof -
 obtain env where runtime: "runtime=[(LPCGoals [],env)]"
 and helper: "(\<lambda>x. env (Inl x))=helper_env"
  using shape by (auto simp: lpc_reinterface_def map_eq_Cons_conv)
 have leaf: "list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (env (Inr slot))) specs"
  using invariant by (simp add: runtime lpp_observer_invariant_def lpc_reinterface_def lpp_leaf_stack_invariant_def)
 have finite: "lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x (\<lambda>i. env (Inr i)))) rest),\<lambda>i. env (Inr i))]"
  using invariant by (simp add: runtime lpp_observer_invariant_def lpc_reinterface_def lpc_attach_answers_def)
 show ?thesis using continuation[OF helper leaf finite]
  by (simp add: runtime lpc_reinterface_def lpc_attach_answers_def)
qed

end
