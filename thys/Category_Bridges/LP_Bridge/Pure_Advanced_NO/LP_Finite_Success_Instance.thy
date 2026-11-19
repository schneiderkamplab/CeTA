theory LP_Finite_Success_Instance
  imports LP_Finite_Success_Pattern_Check
begin

lemma lp_finite_pattern_transport:
  fixes sig local_sig mu local_mu theta eta :: "('f,'v) subst"
  assumes commute: "theta \<circ>\<^sub>s sig = local_sig \<circ>\<^sub>s theta"
    and close: "theta \<circ>\<^sub>s mu = local_mu \<circ>\<^sub>s eta"
  shows "lp_finite_pattern_env theta ((lp_finite_pattern_env sig^^n) (lp_finite_pattern_env mu r)) =
    (lp_finite_pattern_env local_sig^^n) (lp_finite_pattern_env local_mu (lp_finite_pattern_env eta r))"
proof -
  have env_commute: "\<And>r. lp_finite_pattern_env theta (lp_finite_pattern_env sig r) =
      lp_finite_pattern_env local_sig (lp_finite_pattern_env theta r)"
    by (simp only: lp_finite_pattern_env_compose commute)
  have move: "\<And>r. lp_finite_pattern_env theta ((lp_finite_pattern_env sig^^n) r) =
    (lp_finite_pattern_env local_sig^^n) (lp_finite_pattern_env theta r)" for n
  proof (induct n)
    case 0 show ?case by simp
  next
    case (Suc n)
    show ?case using Suc.hyps
      by (simp add: funpow_Suc_right env_commute)
  qed
  have env_close: "lp_finite_pattern_env theta (lp_finite_pattern_env mu r) =
      lp_finite_pattern_env local_mu (lp_finite_pattern_env eta r)"
    by (simp only: lp_finite_pattern_env_compose close)
  show ?thesis by (simp only: move env_close)
qed


theorem lp_finite_success_instance_check_sound:
  assumes ok: "lp_success_instance_check P A sig mu B local_sig local_mu theta eta tsb nu basetrace steps"
  shows "(lp_finite_atom_eval A ((lp_finite_pattern_env (mk_subst Var sig)^^n)
      (lp_finite_pattern_env (mk_subst Var mu) r))#tail,tail)\<in>(lp_ld P)\<^sup>*"
proof -
  have atom: "A=lp_atom_subst B (mk_subst Var theta)"
    and commute: "mk_subst Var theta \<circ>\<^sub>s mk_subst Var sig =
      mk_subst Var local_sig \<circ>\<^sub>s mk_subst Var theta"
    and close: "mk_subst Var theta \<circ>\<^sub>s mk_subst Var mu =
      mk_subst Var local_mu \<circ>\<^sub>s mk_subst Var eta"
    and checked: "lp_success_pattern_check P B local_sig tsb local_mu nu basetrace steps"
    using ok by (auto simp: lp_success_instance_check_def)
  have transport: "lp_finite_pattern_env (mk_subst Var theta)
      ((lp_finite_pattern_env (mk_subst Var sig)^^n) (lp_finite_pattern_env (mk_subst Var mu) r)) =
      (lp_finite_pattern_env (mk_subst Var local_sig)^^n)
        (lp_finite_pattern_env (mk_subst Var local_mu) (lp_finite_pattern_env (mk_subst Var eta) r))"
    by (rule lp_finite_pattern_transport[OF commute close])
  show ?thesis using lp_finite_success_pattern_check_sound[OF checked, of n
      "lp_finite_pattern_env (mk_subst Var eta) r" tail]
    by (simp only: atom lp_atom_subst_comp lp_finite_pattern_env_def[symmetric] transport)
qed


end
