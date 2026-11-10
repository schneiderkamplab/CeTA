theory LP_Finite_Pattern_Trace
  imports LP_Finite_Success_Instance
begin

theorem lp_finite_pattern_run_sound:
  fixes n :: nat and r :: "'v \<Rightarrow> ('f,'v) term"
    and P :: "('f,'v) lp_clause list"
  assumes run: "lp_pattern_run P sig mu gs steps = Some hs"
  defines "env \<equiv> (lp_finite_pattern_env (mk_subst Var sig)^^n)
    (lp_finite_pattern_env (mk_subst Var mu) r)"
  shows "(map (\<lambda>a. lp_finite_atom_eval a env) gs @ tail,
      map (\<lambda>a. lp_finite_atom_eval a env) hs @ tail)\<in>(lp_ld P)\<^sup>*"
  using run
proof (induct steps arbitrary: gs)
  case Nil then show ?case by simp
next
  case (Cons step rest)
  show ?case
  proof (cases step)
    case (LPPatternResolve trace)
    obtain middle where first: "lp_match_run P gs trace=Some middle"
      and remaining: "lp_pattern_run P sig mu middle rest=Some hs"
      using Cons.prems by (auto simp: LPPatternResolve split: option.splits)
    show ?thesis by (rule rtrancl_trans[OF lp_finite_match_run_sound[OF first] Cons.hyps[OF remaining]])
  next
    case (LPPatternSuccess tsb nu basetrace trace)
    obtain a more where gs: "gs=a#more"
      and checked: "lp_success_pattern_check P a sig tsb mu nu basetrace trace"
      and remaining: "lp_pattern_run P sig mu more rest=Some hs"
      using Cons.prems by (auto simp: LPPatternSuccess split: list.splits if_splits)
    have first: "(map (\<lambda>a. lp_finite_atom_eval a env) gs @ tail,
        map (\<lambda>a. lp_finite_atom_eval a env) more @ tail)\<in>(lp_ld P)\<^sup>*"
      using lp_finite_success_pattern_check_sound[OF checked, of n r
          "map (\<lambda>a. lp_finite_atom_eval a env) more @ tail"]
      by (simp add: gs env_def)
    show ?thesis by (rule rtrancl_trans[OF first Cons.hyps[OF remaining]])
  next
    case (LPPatternInstance B ls lm theta eta tsb nu basetrace trace)
    obtain a more where gs: "gs=a#more"
      and checked: "lp_success_instance_check P a sig mu B ls lm theta eta tsb nu basetrace trace"
      and remaining: "lp_pattern_run P sig mu more rest=Some hs"
      using Cons.prems by (auto simp: LPPatternInstance split: list.splits if_splits)
    have first: "(map (\<lambda>a. lp_finite_atom_eval a env) gs @ tail,
        map (\<lambda>a. lp_finite_atom_eval a env) more @ tail)\<in>(lp_ld P)\<^sup>*"
      using lp_finite_success_instance_check_sound[OF checked, of n r
          "map (\<lambda>a. lp_finite_atom_eval a env) more @ tail"]
      by (simp add: gs env_def)
    show ?thesis by (rule rtrancl_trans[OF first Cons.hyps[OF remaining]])
  qed
qed


theorem lp_finite_pattern_trace_loop:
  fixes P :: "('f,'v) lp_clause list" and r :: "'v \<Rightarrow> ('f,'v) term"
  assumes first: "lp_match_run P [A] initial_steps=Some gs"
    and progress: "initial_steps\<noteq>[]"
    and rest: "lp_pattern_run P sig mu gs steps=Some (lp_atom_subst A (mk_subst Var sig)#bs)"
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
        ?F (Suc n)#(map (\<lambda>a. lp_finite_atom_eval a (?E n)) bs @ tail))\<in>(lp_ld P)\<^sup>*"
      using lp_finite_pattern_run_sound[OF rest, of n r tail]
      by (simp add: lp_atom_subst_comp lp_finite_pattern_env_def funpow_Suc_right)
    have path: "(qs,?F (Suc n)#(map (\<lambda>a. lp_finite_atom_eval a (?E n)) bs @ tail))\<in>(lp_ld P)\<^sup>+"
      by (rule trancl_rtrancl_trancl[OF first' rest'])
    show "\<exists>t\<in>?X. (qs,t)\<in>(lp_ld P)\<^sup>+" using path by blast
  qed
  show ?thesis using bad SN_on_trancl
    by (auto simp: lp_atom_subst_comp lp_finite_pattern_env_def)
qed


theorem lp_finite_pattern_loop_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_pattern_loop_check P q arity positions A sig mu firststeps steps"
  shows "\<exists>ts :: ('f,'v) term list. length ts=arity \<and>
    (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
proof -
  let ?initial = "lp_atom_subst A (mk_subst Var mu)"
  have query: "fst ?initial=q" "length (snd ?initial)=arity"
      "\<forall>i\<in>set positions. i<arity \<and> ground (snd ?initial!i)"
    and progress: "firststeps\<noteq>[]"
    using ok by (auto simp: lp_pattern_loop_check_def Let_def list_all_iff)
  obtain gs bs where first: "lp_match_run P [A] firststeps=Some gs"
    and rest: "lp_pattern_run P sig mu gs steps=Some (lp_atom_subst A (mk_subst Var sig)#bs)"
    using ok by (auto simp: lp_pattern_loop_check_def Let_def split: option.splits list.splits)
  have bad: "\<not>SN_on (lp_ld P) {[lp_finite_atom_eval ?initial Var]}"
    by (rule lp_finite_pattern_trace_loop[OF first progress rest])
  show ?thesis by (rule exI[of _ "snd ?initial"])
    (use query bad in \<open>auto simp: lp_atom_subst_def\<close>)
qed


end
