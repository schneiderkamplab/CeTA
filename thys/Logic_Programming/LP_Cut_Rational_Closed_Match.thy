theory LP_Cut_Rational_Closed_Match
  imports LP_Cut_Rational_Free_MGU LP_Rational_Closed_Graph
begin

text \<open>Matching a closed, possibly infinite runtime atom against a source
head is an actual MGU when all body variables occur in that head. This does not
permit instantiating fresh body variables or any saved alternative.\<close>
theorem lpc_closed_match_most_general:
  fixes a :: "('f,string) lp_iterm"
  assumes closed: "\<And>sigma. lp_isubst a sigma=a"
    and matched: "lp_ieval h rho=a"
    and body: "\<And>g t. g\<in>set bs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow>
      vars_term t\<subseteq>vars_term h"
  shows "lpc_mgu_resolve a gs h bs LPIVar rho"
  unfolding lpc_mgu_resolve_def
proof (intro conjI allI impI)
  show "lp_isubst a LPIVar=lp_ieval h rho" using matched by simp
next
  fix tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume comparison: "lp_isubst a tau=lp_ieval h nu"
  have equal_head: "lp_ieval h (\<lambda>x. lp_isubst (rho x) tau)=lp_ieval h nu"
    using comparison matched by (simp add: lp_ieval_subst[symmetric])
  have factor: "lp_isubst (rho x) tau=nu x" if "x\<in>vars_term h" for x
    by (rule lpc_ieval_variables_eq[OF equal_head that])
  have term_factor: "lp_isubst (lp_ieval t rho) tau=lp_ieval t nu"
    if "vars_term t\<subseteq>vars_term h" for t
    unfolding lp_ieval_subst by (rule lp_ieval_cong) (use factor that in auto)
  have body_factor: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) tau)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
  proof (rule map_cong[OF refl])
    fix g assume member: "g\<in>set bs"
    show "lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) tau) g =
      lp_cut_map (\<lambda>t. lp_ieval t nu) g"
      using body[OF member] term_factor by (cases g) auto
  qed
  show "\<exists>delta. lp_isubst (lp_isubst a LPIVar) delta=lp_isubst a tau \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t LPIVar) delta)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
    by (rule exI[of _ tau]) (simp add: body_factor)
qed

ML \<open>
val checked = [@{thm lpc_closed_match_most_general}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted closed rational match dependency" else ();
\<close>
end
