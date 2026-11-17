theory LP_Prolog_Finite_Goal_Transport
 imports LP_Prolog_Finite_Arithmetic_Domain
begin

definition lpp_finite_goals where
 "lpp_finite_goals gs = list_all (\<lambda>g. list_all lpp_finite_term (lp_cut_terms g)) gs"

lemma lpp_finite_goal_bind_terms:
 "lp_cut_terms (lp_cut_bind m f g)=map f (lp_cut_terms g)"
 by (cases g) auto

lemma lpp_finite_goals_initial:
 "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)"
 by (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff
     intro: lpp_finite_term_initial)

lemma lpp_variable_head_finite_goals:
 assumes mgu: "lpc_mgu_resolve (LPIFun f actuals) gs (Fun f (map Var H)) bs sigma rho"
   and lengths: "length H=length actuals" and distinct: "distinct H"
   and arguments: "list_all lpp_finite_term actuals"
   and continuation: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 have body: "lpp_finite_term (lp_ieval t rho)" if "g\<in>set bs" "t\<in>set (lp_cut_terms g)" for g t
   by (rule lpp_variable_head_finite_body[OF mgu lengths distinct arguments that])
 have old: "lpp_finite_term t" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   using continuation that by (auto simp: lpp_finite_goals_def list_all_iff)
 have rest: "lpp_finite_term (lp_isubst t sigma)" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   by (rule lpp_variable_head_finite_continuation[OF mgu lengths distinct old that])
 show ?thesis using body rest
   by (auto simp: lpp_finite_goals_def lpp_finite_goal_bind_terms lpp_finite_goal_map list_all_iff)
qed

lemma lpp_stable_is_finite_goals:
 assumes success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu)"
   and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs)"
 using finite lpp_stable_is_finite_substitution[OF success]
 by (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff)

ML \<open>
val checked = [@{thm lpp_finite_goals_initial}, @{thm lpp_variable_head_finite_goals},
 @{thm lpp_stable_is_finite_goals}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite goal transport" else ();
\<close>
end
