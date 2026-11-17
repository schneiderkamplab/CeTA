theory LP_Prolog_Separation_Fresh_Clause
 imports LP_Prolog_Separation_Resolution_Contract LP_Prolog_Functor_Finite_Unification
begin

lemma lpp_separation_clause_environment:
 assumes known: "lpp_separation_holds rho observation"
 shows "lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)
   (lpp_separation_subst observation (\<lambda>x. Var (lp_prefix l x)))"
 using known by (cases observation) (simp add: lp_cut_resolution_clause)

lemma lpp_fresh_univ_acquires_clause_separation:
 assumes checked: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 shows "list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho))
   (map (\<lambda>observation. lpp_separation_subst observation (\<lambda>x. Var (lp_prefix l x)))
     [LPPSeparate (Var x) (Var y),LPPSeparate (Var x) (Var z)])"
 using lpp_fresh_univ_acquires_separation[OF checked mgu finite]
   lpp_separation_clause_environment[where k=k and l=l and eta=eta and sigma=sigma]
 by (auto simp: list_all_iff lp_cut_resolution_env_def lp_prefix_def)

lemma lpp_matching_head_finite_call_instance:
 assumes matching: "lp_cut_check_match a h bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta) gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_ieval a eta)"
 shows "lpp_finite_term (lp_isubst (lp_ieval a eta) sigma)"
proof -
 have matched: "lp_ieval h (\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) eta)=lp_ieval a eta"
   using matching unfolding lp_cut_check_match_def by (simp add: lp_ieval_finite_subst[symmetric])
 have head: "lpp_finite_term (lp_ieval h rho)"
   by (rule lpp_matching_head_finite_instance[OF mgu matched finite])
 show ?thesis using head mgu by (simp add: lpc_mgu_resolve_def)
qed

ML \<open>
val checked = @{thms lpp_separation_clause_environment lpp_fresh_univ_acquires_clause_separation
 lpp_matching_head_finite_call_instance};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted fresh-clause separation" else ();
\<close>
end
