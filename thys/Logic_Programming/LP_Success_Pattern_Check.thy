theory LP_Success_Pattern_Check
  imports LP_Success_Pattern
begin

definition lp_success_pattern_check where
  "lp_success_pattern_check P A sig tsb mu nu base_steps step_steps =
    (lp_match_run P [lp_atom_subst A (mk_subst Var mu)] base_steps = Some [] \<and>
     lp_match_run P [lp_atom_subst A (mk_subst Var sig)] step_steps =
       Some [lp_atom_subst A (mk_subst Var tsb)] \<and>
     commutes_impl tsb sig \<and>
     subst_eq (subst_compose_impl tsb mu) (subst_compose_impl mu nu))"

theorem lp_success_pattern_check_sound:
  assumes ok: "lp_success_pattern_check P A sig tsb mu nu base_steps step_steps"
  shows "(lp_atom_eval A ((lp_pattern_env (mk_subst Var sig)^^n)
      (lp_pattern_env (mk_subst Var mu) r))#tail,tail)\<in>(lp_ild P)\<^sup>*"
  by (rule lp_match_success_pattern[where tau="mk_subst Var tsb" and nu="mk_subst Var nu"
        and base_steps=base_steps and step_steps=step_steps])
    (use ok in \<open>auto simp: lp_success_pattern_check_def\<close>)

end
