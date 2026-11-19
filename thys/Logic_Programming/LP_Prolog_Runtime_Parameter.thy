theory LP_Prolog_Runtime_Parameter
 imports LP_Prolog_Parameter_Return_Composition LP_Prolog_Stable_Builtins
begin

text \<open>The initial parameter is a finite ground term, not necessarily a
scalar. Keep its identity while changing runtime coordinates. In particular,
groundness at a recursive entry initializes a new local contract; relating it
back to an enclosing contract requires the composition rule below.\<close>

definition lpp_runtime_parameter where
 "lpp_runtime_parameter c value =
  (vars_term c={} \<and> (\<exists>d. lpp_parameter_return c d \<and> value=lp_ieval d LPIVar))"

lemma lpp_runtime_parameter_initial:
 "vars_term c={} \<Longrightarrow> lpp_runtime_parameter c (lp_ieval c LPIVar)"
 by (auto simp: lpp_runtime_parameter_def lpp_parameter_return_def)

lemma lpp_runtime_parameter_ground:
 "lpp_runtime_parameter c value \<Longrightarrow> lp_seg_ground value"
 by (auto simp: lpp_runtime_parameter_def lpp_parameter_return_def lp_seg_ground_eval)

lemma lpp_runtime_parameter_subst:
 assumes tracked: "lpp_runtime_parameter c value"
 shows "lpp_runtime_parameter c (lp_isubst value sigma)"
 using tracked by (simp add: lp_seg_ground_subst[OF lpp_runtime_parameter_ground[OF tracked]])

lemma lpp_runtime_parameter_compose:
 assumes parent: "lpp_runtime_parameter c (lp_ieval d LPIVar)"
 and child: "lpp_runtime_parameter d value"
 shows "lpp_runtime_parameter c value"
 using parent child lpp_parameter_return_transitive lp_seg_ieval_injective
 unfolding lpp_runtime_parameter_def by blast

lemma lpp_runtime_parameter_scalar:
 assumes ground: "vars_term c={}"
 and success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess sigma)"
 shows "lpp_runtime_parameter c (lp_isubst a sigma)"
 using lpp_stable_is_parameter_return[OF success] ground
 by (auto simp: lpp_runtime_parameter_def)

definition lpp_check_parameter_entry where
 "lpp_check_parameter_entry G ctx parameter =
  (vars_term parameter \<subseteq> set G \<union> lpp_source_context_ground ctx)"

lemma lpp_checked_parameter_entry:
 assumes checked: "lpp_check_parameter_entry G ctx parameter"
 and known: "lp_cut_knowledge (set G) K eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 shows "\<exists>c. lp_ieval parameter eta=lp_ieval c LPIVar \<and>
  lpp_runtime_parameter c (lp_ieval parameter eta)"
proof -
 have ground: "lp_seg_ground (lp_ieval parameter eta)"
  using checked known lpp_stable_context_ground_sound[OF observed]
  by (auto simp: lpp_check_parameter_entry_def lp_cut_knowledge_def lp_seg_ground_eval)
 obtain c where closed: "vars_term c={}" and represented: "lp_ieval c LPIVar=lp_ieval parameter eta"
  using lp_seg_ground_finite[OF ground] by (auto simp: ground_vars_term_empty)
 show ?thesis by (rule exI[of _ c])
  (use lpp_runtime_parameter_initial[OF closed] represented in auto)
qed

definition lpp_check_parameter_coordinate where
 "lpp_check_parameter_coordinate source_term target_term bindings = (target_term \<cdot> bindings=source_term)"

lemma lpp_checked_parameter_coordinate_value:
 "lpp_check_parameter_coordinate source_term target_term bindings \<Longrightarrow>
  lp_ieval target_term (\<lambda>x. lp_ieval (bindings x) eta)=lp_ieval source_term eta"
 by (simp add: lpp_check_parameter_coordinate_def lp_ieval_finite_subst[symmetric])

lemma lpp_checked_parameter_coordinate:
 assumes checked: "lpp_check_parameter_coordinate source_term target_term bindings"
 and parameter: "lpp_runtime_parameter c (lp_ieval source_term eta)"
 shows "lpp_runtime_parameter c (lp_ieval target_term (\<lambda>x. lp_ieval (bindings x) eta))"
 using checked parameter
 by (simp add: lpp_check_parameter_coordinate_def lp_ieval_finite_subst[symmetric])

lemma lpp_checked_parameter_coordinate_after_substitution:
 assumes checked: "lpp_check_parameter_coordinate source_term target_term bindings"
 and parameter: "lpp_runtime_parameter c (lp_ieval source_term eta)"
 shows "lpp_runtime_parameter c
  (lp_ieval target_term (\<lambda>x. lp_isubst (lp_ieval (bindings x) eta) sigma))"
 using lpp_runtime_parameter_subst[OF lpp_checked_parameter_coordinate[OF checked parameter]]
 by (simp add: lp_ieval_subst)

lemma lpp_runtime_parameter_ground_is_not_enough:
 "lp_seg_ground (LPIFun (2::nat) [LPIFun 3 []] :: (nat,unit) lp_iterm) \<and>
  \<not> lpp_runtime_parameter (Fun 4 []) (LPIFun 2 [LPIFun 3 []] :: (nat,unit) lp_iterm)"
 by (auto simp: lpp_runtime_parameter_def lpp_parameter_return_def)

lemma lpp_parameter_entry_context_positive:
 "lpp_check_parameter_entry [] ([],[],[LPPOGround (Var (1::nat))]) (Var 1)"
 by (simp add: lpp_check_parameter_entry_def lpp_observations_ground_def)

lemma lpp_parameter_entry_missing_context_negative:
 "\<not> lpp_check_parameter_entry [] ([],[],[]) (Var (1::nat))"
 by (simp add: lpp_check_parameter_entry_def lpp_observations_ground_def)

lemma lpp_parameter_coordinate_positive:
 "lpp_check_parameter_coordinate (Var (1::nat)) (Var (7::nat)) (\<lambda>_. Var 1)"
 by (simp add: lpp_check_parameter_coordinate_def)

lemma lpp_parameter_coordinate_wrong_negative:
 "\<not> lpp_check_parameter_coordinate (Var (1::nat)) (Var (7::nat)) (\<lambda>_. Var 2)"
 by (simp add: lpp_check_parameter_coordinate_def)

ML \<open>
val checked = @{thms lpp_runtime_parameter_initial lpp_runtime_parameter_ground
 lpp_runtime_parameter_subst lpp_runtime_parameter_compose lpp_runtime_parameter_scalar
 lpp_checked_parameter_entry lpp_checked_parameter_coordinate_value lpp_checked_parameter_coordinate
 lpp_checked_parameter_coordinate_after_substitution
 lpp_runtime_parameter_ground_is_not_enough lpp_parameter_entry_context_positive
 lpp_parameter_entry_missing_context_negative lpp_parameter_coordinate_positive
 lpp_parameter_coordinate_wrong_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted runtime parameter invariant" else ();
\<close>
end
