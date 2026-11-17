theory LP_Prolog_Functor_Spine_Return
 imports LP_Prolog_Univ_Ground_Receipt
begin

text \<open>These observations count only actual list cells. Helper calls may
  instantiate rational elements without changing the observed spine. Termination
  of the helper and finite-tree invariants remain separate obligations.\<close>

lemma lpp_univ_success_argument_length:
 assumes outcome: "lpp_univ_view_outcome names (LPIFun f ts)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [name_term,arglist]) (LPPBuiltinSuccess mu)"
 shows "lpp_list_length (lp_isubst arglist mu) (length ts)"
proof -
 have relation: "lpp_functor_observation names (lp_isubst (LPIFun f ts) mu)
   (lp_isubst name_term mu) (lp_isubst arglist mu)"
  by (rule lpp_univ_view_success_observation[OF outcome])
 have args: "lp_isubst arglist mu=lpp_argument_list (map (\<lambda>t. lp_isubst t mu) ts)"
  using relation by (simp add: lpp_functor_observation_exact)
 show ?thesis using lpp_argument_list_length[of "map (\<lambda>t. lp_isubst t mu) ts"]
  by (simp add: args)
qed

lemma lpp_actual_return_preserves_list_length:
 assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and initialized: "list_all (\<lambda>frame. lpp_list_length (lp_ieval template (snd frame)) n) ss"
 shows "lpp_list_length (lp_ieval template eta) n"
 by (rule lpp_actual_return_substitution_property[where
       F="\<lambda>rho. lpp_list_length (lp_ieval template rho) n", OF _ actual initialized])
   (auto simp: lp_ieval_subst[symmetric] intro: lpp_list_length_subst)

lemma lpp_actual_return_list_tail_descent:
 assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and initialized: "list_all (\<lambda>frame. lpp_list_length
   (lp_ieval (Fun (LPCUser ''2:prolog_data_2e'') [head_term,tail_term]) (snd frame)) (Suc n)) ss"
 shows "lpp_list_length (lp_ieval tail_term eta) n \<and> n<Suc n"
proof -
 have tails: "list_all (\<lambda>frame. lpp_list_length (lp_ieval tail_term (snd frame)) n) ss"
  using initialized by (auto simp: list_all_iff elim: lpp_list_length.cases)
 show ?thesis using lpp_actual_return_preserves_list_length[OF actual tails] by simp
qed

lemma lpp_spine_return_does_not_make_elements_finite:
 assumes cyclic: "t=LPIFun f [t]"
 shows "lpp_list_length (lpp_argument_list [t]) 1 \<and> \<not>lpp_finite_term (lpp_argument_list [t])"
 using lpp_cyclic_child_finite_spine_only[OF cyclic] by blast

ML \<open>
val checked = @{thms lpp_univ_success_argument_length lpp_actual_return_preserves_list_length
 lpp_actual_return_list_tail_descent lpp_spine_return_does_not_make_elements_finite};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor spine return" else ();
\<close>
end
