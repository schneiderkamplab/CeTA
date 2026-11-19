theory LP_Finite_Affine_Loop
  imports LP_Finite_Affine_Success
begin

lemma lp_finite_affine_run_sound:
  assumes "lp_affine_run P c z env gs steps=Some hs"
  shows "(map (\<lambda>A. lp_finite_atom_eval A (lp_finite_aenv c z env n m)) gs @ tail,
    map (\<lambda>A. lp_finite_atom_eval A (lp_finite_aenv c z env n m)) hs @ tail)\<in>(lp_ld P)\<^sup>*"
  using assms
proof (induct steps arbitrary: gs)
  case Nil then show ?case by simp
next
  case (Cons step rest)
  show ?case
  proof (cases step)
    case (LPAffineResolve trace)
    obtain middle where first: "lp_match_run P gs trace=Some middle"
      and remaining: "lp_affine_run P c z env middle rest=Some hs"
      using Cons.prems by (auto simp: LPAffineResolve split: option.splits)
    show ?thesis by (rule rtrancl_trans[OF lp_finite_match_run_sound[OF first] Cons.hyps[OF remaining]])
  next
    case (LPAffineSuccess B sig mu tsb nu basetrace trace idx rho)
    obtain A more where gs: "gs=A#more"
      and checked: "lp_affine_success_check P c z env A B sig mu tsb nu basetrace trace idx (lp_alook rho)"
      and remaining: "lp_affine_run P c z env more rest=Some hs"
      using Cons.prems by (auto simp: LPAffineSuccess split: list.splits if_splits)
    have first: "(map (\<lambda>A. lp_finite_atom_eval A (lp_finite_aenv c z env n m)) gs @ tail,
        map (\<lambda>A. lp_finite_atom_eval A (lp_finite_aenv c z env n m)) more @ tail)\<in>(lp_ld P)\<^sup>*"
      using lp_finite_affine_success_sound[OF checked, of n m
          "map (\<lambda>A. lp_finite_atom_eval A (lp_finite_aenv c z env n m)) more @ tail"] by (simp add: gs)
    show ?thesis by (rule rtrancl_trans[OF first Cons.hyps[OF remaining]])
  qed
qed


lemma lp_finite_affine_closed_sound:
  assumes "lp_affine_closed c z env A C u v"
  shows "lp_finite_atom_eval C (lp_finite_aenv c z env n m)=
    lp_finite_atom_eval A (lp_finite_aenv c z env (lp_aeval u n m) (lp_aeval v n m))"
proof -
  obtain f es where lhs: "lp_word_atom c z env C=Some (f,es)"
    and rhs: "lp_word_atom c z (\<lambda>x. lp_acomp (env x) u v) A=Some (f,es)"
    using assms by (auto simp: lp_affine_closed_def split: option.splits)
  have env: "lp_finite_aenv c z (\<lambda>x. lp_acomp (env x) u v) n m =
      lp_finite_aenv c z env (lp_aeval u n m) (lp_aeval v n m)"
    by (rule ext) (simp add: lp_finite_aenv_def)
  have "lp_finite_atom_eval C (lp_finite_aenv c z env n m)=(f,map (\<lambda>a. lp_finite_word c z (lp_aeval a n m)) es)"
    by (rule lp_finite_word_atom_sound[OF lhs])
  also have "...=lp_finite_atom_eval A (lp_finite_aenv c z (\<lambda>x. lp_acomp (env x) u v) n m)"
    by (rule sym, rule lp_finite_word_atom_sound[OF rhs])
  also have "...=lp_finite_atom_eval A (lp_finite_aenv c z env (lp_aeval u n m) (lp_aeval v n m))"
    by (simp only: env)
  finally show ?thesis .
qed


lemma lp_finite_affine_trace_loop:
  fixes P :: "('f,'v) lp_clause list"
  assumes first: "lp_match_run P [A] firststeps=Some gs" and progress: "firststeps\<noteq>[]"
    and rest: "lp_affine_run P c z env gs steps=Some (C#bs)"
    and closed: "lp_affine_closed c z env A C u v"
  shows "\<not>SN_on (lp_ld P) {[lp_finite_atom_eval A (lp_finite_aenv c z env 0 0)]}"
proof -
  let ?F = "\<lambda>n m. lp_finite_atom_eval A (lp_finite_aenv c z env n m)"
  let ?X = "{qs :: ('f,'v) lp_atom list. \<exists>n m tail. qs=?F n m#tail}"
  have bad: "\<not>SN_on ((lp_ld P)\<^sup>+) {[?F 0 0]}"
  proof (rule lp_serial_not_SN[where X="?X"])
    show "[?F 0 0]\<in>?X" by blast
  next
    fix qs assume "qs\<in>?X"
    then obtain n m tail where qs: "qs=?F n m#tail" by blast
    have first': "(qs,map (\<lambda>a. lp_finite_atom_eval a (lp_finite_aenv c z env n m)) gs @ tail)\<in>(lp_ld P)\<^sup>+"
      using lp_finite_match_run_nonempty_sound[OF first progress, of "lp_finite_aenv c z env n m" tail]
      by (simp add: qs)
    have rest': "(map (\<lambda>a. lp_finite_atom_eval a (lp_finite_aenv c z env n m)) gs @ tail,
      ?F (lp_aeval u n m) (lp_aeval v n m)#
        (map (\<lambda>a. lp_finite_atom_eval a (lp_finite_aenv c z env n m)) bs @ tail))\<in>(lp_ld P)\<^sup>*"
      apply (subst lp_finite_affine_closed_sound[OF closed, symmetric])
      using lp_finite_affine_run_sound[OF rest, of n m tail] by simp
    show "\<exists>t\<in>?X. (qs,t)\<in>(lp_ld P)\<^sup>+"
      using trancl_rtrancl_trancl[OF first' rest'] by blast
  qed
  show ?thesis using bad SN_on_trancl by auto
qed


theorem lp_finite_affine_loop_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_affine_loop_check P q arity positions c z env A firststeps steps u v"
  shows "\<exists>ts :: ('f,'v) term list. length ts=arity \<and>
    (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
proof -
  obtain es gs C bs where atom: "lp_word_atom c z (lp_alook env) A=Some (q,es)"
    and arity: "length es=arity" and positions: "\<forall>i\<in>set positions. i<arity"
    and first: "lp_match_run P [A] firststeps=Some gs" and progress: "firststeps\<noteq>[]"
    and rest: "lp_affine_run P c z (lp_alook env) gs steps=Some (C#bs)"
    and closed: "lp_affine_closed c z (lp_alook env) A C u v"
    using ok by (auto simp: lp_affine_loop_check_def list_all_iff split: option.splits list.splits)
  let ?ts = "map (\<lambda>a. lp_word_term c z (lp_aeval a 0 0)) es"
  have bad: "\<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ?ts)]}"
  proof -
    have equal: "lp_finite_atom_eval A (lp_finite_aenv c z (lp_alook env) 0 0)=
        (q,map (\<lambda>t. lp_finite_eval t Var) ?ts)"
      using lp_finite_word_atom_sound[OF atom, of 0 0]
      by (simp add: o_def lp_finite_word_eq_term)
    show ?thesis unfolding equal[symmetric]
      by (rule lp_finite_affine_trace_loop[OF first progress rest closed])
  qed
  show ?thesis by (rule exI[of _ ?ts]) (use arity positions bad in \<open>auto simp: nth_map\<close>)
qed


end
