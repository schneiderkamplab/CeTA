theory LP_Finite_Pattern_Acceleration
  imports LP_Finite_Pattern_Trace
begin

lemma lp_finite_pattern_env_power:
  "lp_finite_pattern_env (mk_subst Var (subst_power_impl sig n)) =
    (lp_finite_pattern_env (mk_subst Var sig)^^n)"
  by (induct n) (simp_all add: lp_finite_pattern_env_def lp_finite_eval_subst
      subst_compose_def fun_eq_iff funpow_Suc_right)


lemma lp_finite_pattern_acceleration_sound:
  assumes ok: "lp_pattern_acceleration_check A C sig mu B ls lm theta eta delta k b"
  shows "lp_finite_atom_eval C ((lp_finite_pattern_env (mk_subst Var sig)^^n)
      (lp_finite_pattern_env (mk_subst Var mu) r)) =
    lp_finite_atom_eval A ((lp_finite_pattern_env (mk_subst Var sig)^^(k*n+b))
      (lp_finite_pattern_env (mk_subst Var mu) r))"
proof -
  have A: "A=lp_atom_subst B (mk_subst Var theta)"
    and C: "C=lp_atom_subst B (mk_subst Var delta)"
    and commute: "mk_subst Var theta \<circ>\<^sub>s mk_subst Var sig =
      mk_subst Var ls \<circ>\<^sub>s mk_subst Var theta"
    and close: "mk_subst Var theta \<circ>\<^sub>s mk_subst Var mu =
      mk_subst Var lm \<circ>\<^sub>s mk_subst Var eta"
    and dcommute: "mk_subst Var delta \<circ>\<^sub>s mk_subst Var sig =
      mk_subst Var (subst_power_impl ls k) \<circ>\<^sub>s mk_subst Var delta"
    and dclose: "mk_subst Var delta \<circ>\<^sub>s mk_subst Var mu =
      mk_subst Var (subst_compose_impl (subst_power_impl ls b) lm) \<circ>\<^sub>s mk_subst Var eta"
    using ok by (auto simp: lp_pattern_acceleration_check_def subst_compose_assoc)
  note source = lp_finite_pattern_transport[OF commute close, of "k*n+b" r]
  note target = lp_finite_pattern_transport[OF dcommute dclose, of n r]
  show ?thesis
    unfolding A C lp_atom_subst_comp lp_finite_pattern_env_def[symmetric]
    apply (subst source)
    apply (subst target)
    by (simp only: subst_compose_impl lp_finite_pattern_env_compose[symmetric]
        lp_finite_pattern_env_power funpow_mult funpow_add o_apply)
qed


theorem lp_finite_pattern_trace_closed:
  fixes P :: "('f,'v) lp_clause list" and r :: "'v \<Rightarrow> ('f,'v) term"
  assumes first: "lp_match_run P [A] initial_steps=Some gs"
    and progress: "initial_steps\<noteq>[]"
    and rest: "lp_pattern_run P sig mu gs steps=Some (C#bs)"
    and closed: "\<And>n. lp_finite_atom_eval C ((lp_finite_pattern_env (mk_subst Var sig)^^n)
        (lp_finite_pattern_env (mk_subst Var mu) r)) =
      lp_finite_atom_eval A ((lp_finite_pattern_env (mk_subst Var sig)^^(f n))
        (lp_finite_pattern_env (mk_subst Var mu) r))"
  shows "\<not>SN_on (lp_ld P) {[lp_finite_atom_eval (lp_atom_subst A (mk_subst Var mu)) r]}"
proof -
  let ?E = "\<lambda>n. (lp_finite_pattern_env (mk_subst Var sig)^^n) (lp_finite_pattern_env (mk_subst Var mu) r)"
  let ?F = "\<lambda>n. lp_finite_atom_eval A (?E n)"
  let ?X = "{qs. \<exists>n tail. qs=?F n#tail}"
  have bad: "\<not>SN_on ((lp_ld P)\<^sup>+) {[?F 0]}"
  proof (rule lp_serial_not_SN[where X="?X"])
    show "[?F 0]\<in>?X" by blast
  next
    fix qs assume "qs\<in>?X"
    then obtain n tail where qs: "qs=?F n#tail" by blast
    have first': "(qs,map (\<lambda>a. lp_finite_atom_eval a (?E n)) gs @ tail)\<in>(lp_ld P)\<^sup>+"
      using lp_finite_match_run_nonempty_sound[OF first progress, of "?E n" tail]
      by (simp add: qs)
    have rest': "(map (\<lambda>a. lp_finite_atom_eval a (?E n)) gs @ tail,
        ?F (f n)#(map (\<lambda>a. lp_finite_atom_eval a (?E n)) bs @ tail))\<in>(lp_ld P)\<^sup>*"
      using lp_finite_pattern_run_sound[OF rest, of n r tail] by (simp add: closed)
    have path: "(qs,?F (f n)#(map (\<lambda>a. lp_finite_atom_eval a (?E n)) bs @ tail))\<in>(lp_ld P)\<^sup>+"
      by (rule trancl_rtrancl_trancl[OF first' rest'])
    show "\<exists>t\<in>?X. (qs,t)\<in>(lp_ld P)\<^sup>+" using path by blast
  qed
  show ?thesis using bad SN_on_trancl
    by (auto simp: lp_atom_subst_comp lp_finite_pattern_env_def)
qed


theorem lp_finite_accelerated_loop_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_accelerated_loop_check P q arity positions A sig mu firststeps steps B ls lm theta eta delta k b"
  shows "\<exists>ts :: ('f,'v) term list. length ts=arity \<and>
    (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
proof -
  let ?initial = "lp_atom_subst A (mk_subst Var mu)"
  have query: "fst ?initial=q" "length (snd ?initial)=arity"
      "\<forall>i\<in>set positions. i<arity \<and> ground (snd ?initial!i)"
    and progress: "firststeps\<noteq>[]"
    using ok by (auto simp: lp_accelerated_loop_check_def Let_def list_all_iff)
  obtain gs C bs where first: "lp_match_run P [A] firststeps=Some gs"
    and rest: "lp_pattern_run P sig mu gs steps=Some (C#bs)"
    and checked: "lp_pattern_acceleration_check A C sig mu B ls lm theta eta delta k b"
    using ok by (auto simp: lp_accelerated_loop_check_def Let_def split: option.splits list.splits)
  have bad: "\<not>SN_on (lp_ld P) {[lp_finite_atom_eval ?initial Var]}"
    by (rule lp_finite_pattern_trace_closed[OF first progress rest lp_finite_pattern_acceleration_sound[OF checked]])
  show ?thesis by (rule exI[of _ "snd ?initial"])
    (use query bad in \<open>auto simp: lp_atom_subst_def\<close>)
qed


end
