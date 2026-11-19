theory LP_Finite_Success_Pattern
  imports LP_Finite_Recurrent_Pair_Check
begin

definition lp_finite_pattern_env where
  "lp_finite_pattern_env s r = (\<lambda>x. lp_finite_eval (s x) r)"


lemma lp_finite_pattern_env_compose:
  "lp_finite_pattern_env s (lp_finite_pattern_env t r) = lp_finite_pattern_env (s \<circ>\<^sub>s t) r"
  by (rule ext) (simp add: lp_finite_pattern_env_def subst_compose_def lp_finite_eval_subst)


theorem lp_finite_match_success_pattern:
  fixes sig tau mu nu :: "('f,'v) subst"
    and A :: "('f,'v) lp_atom"
    and r :: "'v \<Rightarrow> ('f,'v) term"
  assumes base: "lp_match_run P [lp_atom_subst A mu] base_steps = Some []"
    and step: "lp_match_run P [lp_atom_subst A sig] step_steps =
      Some [lp_atom_subst A tau]"
    and commute: "tau \<circ>\<^sub>s sig = sig \<circ>\<^sub>s tau"
    and close: "tau \<circ>\<^sub>s mu = mu \<circ>\<^sub>s nu"
  shows "(lp_finite_atom_eval A ((lp_finite_pattern_env sig^^n) (lp_finite_pattern_env mu r))#tail,
      tail)\<in>(lp_ld P)\<^sup>*"
proof (rule lp_success_pattern_induct[where A="lp_finite_atom_eval A" and S="lp_finite_pattern_env sig"
    and M="lp_finite_pattern_env mu" and T="lp_finite_pattern_env tau" and N="lp_finite_pattern_env nu"
    and R="lp_ld P"])
  fix r :: "'v \<Rightarrow> ('f,'v) term" and tail
  show "(lp_finite_atom_eval A (lp_finite_pattern_env mu r)#tail,tail)\<in>(lp_ld P)\<^sup>*"
    using lp_finite_match_run_sound[OF base, of r tail]
    by (simp add: lp_atom_subst_comp lp_finite_pattern_env_def)
next
  fix r :: "'v \<Rightarrow> ('f,'v) term" and tail
  show "(lp_finite_atom_eval A (lp_finite_pattern_env sig r)#tail,
      lp_finite_atom_eval A (lp_finite_pattern_env tau r)#tail)\<in>(lp_ld P)\<^sup>*"
    using lp_finite_match_run_sound[OF step, of r tail]
    by (simp add: lp_atom_subst_comp lp_finite_pattern_env_def)
next
  fix r
  show "lp_finite_pattern_env tau (lp_finite_pattern_env sig r) = lp_finite_pattern_env sig (lp_finite_pattern_env tau r)"
    by (simp only: lp_finite_pattern_env_compose commute)
next
  fix r
  show "lp_finite_pattern_env tau (lp_finite_pattern_env mu r) = lp_finite_pattern_env mu (lp_finite_pattern_env nu r)"
    by (simp only: lp_finite_pattern_env_compose close)
qed


end
