theory LP_Finite_Success_Pattern_Check
  imports LP_Finite_Success_Pattern
begin

theorem lp_finite_success_pattern_check_sound:
  assumes ok: "lp_success_pattern_check P A sig tsb mu nu base_steps step_steps"
  shows "(lp_finite_atom_eval A ((lp_finite_pattern_env (mk_subst Var sig)^^n)
      (lp_finite_pattern_env (mk_subst Var mu) r))#tail,tail)\<in>(lp_ld P)\<^sup>*"
  by (rule lp_finite_match_success_pattern[where tau="mk_subst Var tsb" and nu="mk_subst Var nu"
        and base_steps=base_steps and step_steps=step_steps])
    (use ok in \<open>auto simp: lp_success_pattern_check_def\<close>)


end
