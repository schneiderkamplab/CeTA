theory LP_Prolog_Separated_Pair_Structure
 imports LP_Prolog_Reflexive_Structure LP_Prolog_Finite_Pair_Unify
begin

text \<open>Binding two distinct fresh outputs to an observed pair preserves
that pair's finite structure. Runtime separation is essential; syntactic
variable-name disjointness is not a substitute for the checked premise.\<close>

lemma lpp_separated_pair_structural_observation:
 assumes mgu: "lpc_mgu_unify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b]) gs sigma"
 and finite: "lpp_finite_term a" "lpp_finite_term b"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 shows "\<exists>observed_tree. lpp_runtime_structure (LPIFun f [a,b]) observed_tree \<and>
   lpp_runtime_structure (lp_isubst (LPIFun f [a,b]) sigma) observed_tree"
proof -
 let ?comparison = "LPIVar(x := a,y := b)"
 have unchanged: "lp_isubst a ?comparison=a" "lp_isubst b ?comparison=b"
  by (rule lpp_finite_term_subst_untouched[OF finite(1)], use fresh in auto,
      rule lpp_finite_term_subst_untouched[OF finite(2)], use fresh in auto)
 have comparison: "lp_isubst (LPIFun f [LPIVar x,LPIVar y]) ?comparison =
   lp_isubst (LPIFun f [a,b]) ?comparison"
  using unchanged distinct by simp
 obtain delta where factor: "lp_isubst (lp_isubst (LPIFun f [LPIVar x,LPIVar y]) sigma) delta =
    lp_isubst (LPIFun f [LPIVar x,LPIVar y]) ?comparison"
  using mgu comparison unfolding lpc_mgu_unify_def by blast
 have unifies: "lp_isubst (LPIFun f [LPIVar x,LPIVar y]) sigma=lp_isubst (LPIFun f [a,b]) sigma"
  using mgu by (simp add: lpc_mgu_unify_def)
 have inverse: "lp_isubst (lp_isubst (LPIFun f [a,b]) sigma) delta=LPIFun f [a,b]"
  using factor unifies distinct by simp
 have fin: "lpp_finite_term (LPIFun f [a,b])" using finite by simp
 show ?thesis by (rule lpp_finite_inverse_structural_observation[OF fin inverse])
qed

ML \<open>
val checked = @{thms lpp_separated_pair_structural_observation};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted separated pair structural transport" else ();
\<close>
end
