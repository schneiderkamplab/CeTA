theory LP_Success_Pattern
  imports LP_Source_Trace LP_Source_Tree "First_Order_Terms.Term_Impl"
begin

text \<open>Uniform successful prefixes, including accumulator recursions.
  The recursive trace is not assumed to finish: induction on the pumping
  exponent supplies its continuation. Both traces preserve the entire tail.
  Commutation and closing compatibility are essential; without the latter,
  an accumulator can invalidate the base case after one iteration.\<close>

lemma lp_success_pattern_induct:
  assumes base: "\<And>r tail. (A (M r)#tail,tail)\<in>R\<^sup>*"
    and step: "\<And>r tail. (A (S r)#tail,A (T r)#tail)\<in>R\<^sup>*"
    and commute: "\<And>r. T (S r)=S (T r)"
    and close: "\<And>r. T (M r)=M (N r)"
  shows "(A ((S^^n) (M r))#tail,tail)\<in>R\<^sup>*"
proof -
  have move: "\<And>r. T ((S^^n) r)=(S^^n) (T r)" for n
    by (induct n) (simp_all add: funpow_Suc_right commute)
  show ?thesis
  proof (induct n arbitrary: r tail)
    case 0 show ?case using base by simp
  next
    case (Suc n)
    have first: "(A ((S^^Suc n) (M r))#tail,
        A ((S^^n) (M (N r)))#tail)\<in>R\<^sup>*"
      using step[of "(S^^n) (M r)" tail]
      by (simp add: funpow_Suc_right move close)
    show ?case by (rule rtrancl_trans[OF first Suc.hyps])
  qed
qed

definition lp_pattern_env where
  "lp_pattern_env s r = (\<lambda>x. lp_ieval (s x) r)"

lemma lp_pattern_env_compose:
  "lp_pattern_env s (lp_pattern_env t r) = lp_pattern_env (s \<circ>\<^sub>s t) r"
  by (rule ext) (simp add: lp_pattern_env_def subst_compose_def lp_ieval_finite_subst)

theorem lp_match_success_pattern:
  fixes sig tau mu nu :: "('f,'v) subst"
    and A :: "('f,'v) lp_atom"
    and r :: "'v \<Rightarrow> ('f,'w) lp_iterm"
  assumes base: "lp_match_run P [lp_atom_subst A mu] base_steps = Some []"
    and step: "lp_match_run P [lp_atom_subst A sig] step_steps =
      Some [lp_atom_subst A tau]"
    and commute: "tau \<circ>\<^sub>s sig = sig \<circ>\<^sub>s tau"
    and close: "tau \<circ>\<^sub>s mu = mu \<circ>\<^sub>s nu"
  shows "(lp_atom_eval A ((lp_pattern_env sig^^n) (lp_pattern_env mu r))#tail,
      tail)\<in>(lp_ild P)\<^sup>*"
proof (rule lp_success_pattern_induct[where A="lp_atom_eval A" and S="lp_pattern_env sig"
    and M="lp_pattern_env mu" and T="lp_pattern_env tau" and N="lp_pattern_env nu"
    and R="lp_ild P"])
  fix r :: "'v \<Rightarrow> ('f,'w) lp_iterm" and tail
  show "(lp_atom_eval A (lp_pattern_env mu r)#tail,tail)\<in>(lp_ild P)\<^sup>*"
    using lp_match_run_sound[OF base, of r tail]
    by (simp add: lp_atom_eval_finite_subst lp_pattern_env_def)
next
  fix r :: "'v \<Rightarrow> ('f,'w) lp_iterm" and tail
  show "(lp_atom_eval A (lp_pattern_env sig r)#tail,
      lp_atom_eval A (lp_pattern_env tau r)#tail)\<in>(lp_ild P)\<^sup>*"
    using lp_match_run_sound[OF step, of r tail]
    by (simp add: lp_atom_eval_finite_subst lp_pattern_env_def)
next
  fix r
  show "lp_pattern_env tau (lp_pattern_env sig r) = lp_pattern_env sig (lp_pattern_env tau r)"
    by (simp only: lp_pattern_env_compose commute)
next
  fix r
  show "lp_pattern_env tau (lp_pattern_env mu r) = lp_pattern_env mu (lp_pattern_env nu r)"
    by (simp only: lp_pattern_env_compose close)
qed

end
