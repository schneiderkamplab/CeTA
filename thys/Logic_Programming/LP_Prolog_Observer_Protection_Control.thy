theory LP_Prolog_Observer_Protection_Control
 imports LP_Prolog_Observer_Term_Test_Node LP_Prolog_Return_Slot_Controls
begin

text \<open>Finite execution and a leaf observation alone do not protect a
caller from helper-output instantiation. A checked fresh-clause acquisition or
an explicit caller-separation premise is necessary at the intervening nodes.\<close>

lemma lpp_observer_invariant_does_not_protect_output:
 fixes x y z :: string and f a pair_symbol :: "string lp_cut_symbol"
 assumes different: "x\<noteq>y" "x\<noteq>z" "y\<noteq>z"
 defines "left_term \<equiv> LPIFun pair_symbol [LPIVar x,LPIVar y]"
 and "right_term \<equiv> LPIFun pair_symbol [LPIFun f [LPIVar z],LPIFun a []]"
 and "sigma \<equiv> LPIVar(x:=LPIFun f [LPIVar z],y:=LPIFun a [])"
 shows "lpp_observer_invariant {u. vars_term u={}} [(0,Fun (Inr ()) [])] [LPCAtom (Var 0)]
   [(LPCGoals [LPCUnify left_term right_term],\<lambda>slot::nat+nat. LPIVar x)]"
 and "lpc_mgu_unify left_term right_term [LPCAtom (LPIVar x)] sigma"
 and "\<not>lpp_runtime_leaf_effect {u. vars_term u={}} (Fun (Inr ()) []) (lp_isubst (LPIVar x) sigma)"
proof -
 have initial: "lpp_runtime_leaf_effect {u::(string lp_cut_symbol,string) term. vars_term u={}}
   (Fun (Inr ()) []) (LPIVar x)"
 proof (rule lpp_runtime_leaf_effect_initial)
  show "lpp_runtime_structure (LPIVar x) (Fun (Inr ()) [])"
   unfolding lpp_runtime_structure_def by (rule exI[of _ "Var x"]) simp
 qed
 show "lpp_observer_invariant {u. vars_term u={}} [(0,Fun (Inr ()) [])] [LPCAtom (Var 0)]
   [(LPCGoals [LPCUnify left_term right_term],\<lambda>slot::nat+nat. LPIVar x)]"
  using initial by (simp add: lpp_observer_invariant_def lpp_leaf_stack_invariant_def
   lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def
   left_term_def right_term_def)
 show "lpc_mgu_unify left_term right_term [LPCAtom (LPIVar x)] sigma"
 and "\<not>lpp_runtime_leaf_effect {u. vars_term u={}} (Fun (Inr ()) []) (lp_isubst (LPIVar x) sigma)"
  using lpp_unprotected_output_leaf_counterexample[where f=f and a=a and pair_symbol=pair_symbol, OF different] different
  by (simp_all add: left_term_def right_term_def sigma_def)
qed

ML \<open>
val checked = @{thms lpp_observer_invariant_does_not_protect_output};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer protection control" else ();
\<close>
end
