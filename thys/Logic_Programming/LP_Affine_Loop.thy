theory LP_Affine_Loop
  imports LP_Affine_Success
begin

datatype ('f,'v) lp_affine_step =
    LPAffineResolve "(nat \<times> ('f,'v) substL) list"
  | LPAffineSuccess "('f,'v) lp_atom" "('f,'v) substL" "('f,'v) substL"
      "('f,'v) substL" "('f,'v) substL"
      "(nat \<times> ('f,'v) substL) list" "(nat \<times> ('f,'v) substL) list"
      lp_affine "('v \<times> lp_affine) list"

fun lp_affine_run where
  "lp_affine_run P c z env gs []=Some gs"
| "lp_affine_run P c z env gs (LPAffineResolve runsteps#rest)=
    (case lp_match_run P gs runsteps of None \<Rightarrow> None | Some hs \<Rightarrow>
      lp_affine_run P c z env hs rest)"
| "lp_affine_run P c z env gs (LPAffineSuccess B sig mu tsb nu basetrace runsteps idx rho#rest)=
    (case gs of [] \<Rightarrow> None | A#tail \<Rightarrow>
      if lp_affine_success_check P c z env A B sig mu tsb nu basetrace runsteps idx (lp_alook rho)
      then lp_affine_run P c z env tail rest else None)"

lemma lp_affine_run_sound:
  assumes "lp_affine_run P c z env gs steps=Some hs"
  shows "(map (\<lambda>A. lp_atom_eval A (lp_aenv c z env n m)) gs @ tail,
    map (\<lambda>A. lp_atom_eval A (lp_aenv c z env n m)) hs @ tail)\<in>(lp_ild P)\<^sup>*"
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
    show ?thesis by (rule rtrancl_trans[OF lp_match_run_sound[OF first] Cons.hyps[OF remaining]])
  next
    case (LPAffineSuccess B sig mu tsb nu basetrace trace idx rho)
    obtain A more where gs: "gs=A#more"
      and checked: "lp_affine_success_check P c z env A B sig mu tsb nu basetrace trace idx (lp_alook rho)"
      and remaining: "lp_affine_run P c z env more rest=Some hs"
      using Cons.prems by (auto simp: LPAffineSuccess split: list.splits if_splits)
    have first: "(map (\<lambda>A. lp_atom_eval A (lp_aenv c z env n m)) gs @ tail,
        map (\<lambda>A. lp_atom_eval A (lp_aenv c z env n m)) more @ tail)\<in>(lp_ild P)\<^sup>*"
      using lp_affine_success_sound[OF checked, of n m
          "map (\<lambda>A. lp_atom_eval A (lp_aenv c z env n m)) more @ tail"] by (simp add: gs)
    show ?thesis by (rule rtrancl_trans[OF first Cons.hyps[OF remaining]])
  qed
qed

definition lp_affine_closed where
  "lp_affine_closed c z env A C u v =
    (case lp_word_atom c z env C of None \<Rightarrow> False | Some result \<Rightarrow>
      lp_word_atom c z (\<lambda>x. lp_acomp (env x) u v) A=Some result)"

lemma lp_affine_closed_sound:
  assumes "lp_affine_closed c z env A C u v"
  shows "lp_atom_eval C (lp_aenv c z env n m)=
    lp_atom_eval A (lp_aenv c z env (lp_aeval u n m) (lp_aeval v n m))"
proof -
  obtain f es where lhs: "lp_word_atom c z env C=Some (f,es)"
    and rhs: "lp_word_atom c z (\<lambda>x. lp_acomp (env x) u v) A=Some (f,es)"
    using assms by (auto simp: lp_affine_closed_def split: option.splits)
  have env: "lp_aenv c z (\<lambda>x. lp_acomp (env x) u v) n m =
      lp_aenv c z env (lp_aeval u n m) (lp_aeval v n m)"
    by (rule ext) (simp add: lp_aenv_def)
  have "lp_atom_eval C (lp_aenv c z env n m)=(f,map (\<lambda>a. lp_word c z (lp_aeval a n m)) es)"
    by (rule lp_word_atom_sound[OF lhs])
  also have "...=lp_atom_eval A (lp_aenv c z (\<lambda>x. lp_acomp (env x) u v) n m)"
    by (rule sym, rule lp_word_atom_sound[OF rhs])
  also have "...=lp_atom_eval A (lp_aenv c z env (lp_aeval u n m) (lp_aeval v n m))"
    by (simp only: env)
  finally show ?thesis .
qed

lemma lp_affine_trace_loop:
  assumes first: "lp_match_run P [A] firststeps=Some gs" and progress: "firststeps\<noteq>[]"
    and rest: "lp_affine_run P c z env gs steps=Some (C#bs)"
    and closed: "lp_affine_closed c z env A C u v"
  shows "\<not>SN_on (lp_ild P) {[lp_atom_eval A (lp_aenv c z env 0 0)]}"
proof -
  let ?F = "\<lambda>n m. lp_atom_eval A (lp_aenv c z env n m)"
  let ?X = "{qs. \<exists>n m tail. qs=?F n m#tail}"
  have bad: "\<not>SN_on ((lp_ild P)\<^sup>+) {[?F 0 0]}"
  proof (rule lp_serial_not_SN[where X="?X"])
    show "[?F 0 0]\<in>?X" by blast
  next
    fix qs assume "qs\<in>?X"
    then obtain n m tail where qs: "qs=?F n m#tail" by blast
    have first': "(qs,map (\<lambda>a. lp_atom_eval a (lp_aenv c z env n m)) gs @ tail)\<in>(lp_ild P)\<^sup>+"
      using lp_match_run_nonempty_sound[OF first progress, of "lp_aenv c z env n m" tail]
      by (simp add: qs)
    have rest': "(map (\<lambda>a. lp_atom_eval a (lp_aenv c z env n m)) gs @ tail,
      ?F (lp_aeval u n m) (lp_aeval v n m)#
        (map (\<lambda>a. lp_atom_eval a (lp_aenv c z env n m)) bs @ tail))\<in>(lp_ild P)\<^sup>*"
      apply (subst lp_affine_closed_sound[OF closed, symmetric])
      using lp_affine_run_sound[OF rest, of n m tail] by simp
    show "\<exists>t\<in>?X. (qs,t)\<in>(lp_ild P)\<^sup>+"
      using trancl_rtrancl_trancl[OF first' rest'] by blast
  qed
  show ?thesis using bad SN_on_trancl by auto
qed

definition lp_affine_loop_check where
  "lp_affine_loop_check P q arity positions c z env A firststeps steps u v =
    (firststeps\<noteq>[] \<and>
     (case lp_word_atom c z (lp_alook env) A of Some (f,es) \<Rightarrow>
       f=q \<and> length es=arity \<and> list_all (\<lambda>i. i<arity) positions \<and>
       (case lp_match_run P [A] firststeps of None \<Rightarrow> False | Some gs \<Rightarrow>
         (case lp_affine_run P c z (lp_alook env) gs steps of Some (C#bs) \<Rightarrow>
           lp_affine_closed c z (lp_alook env) A C u v | _ \<Rightarrow> False))
       | _ \<Rightarrow> False))"

theorem lp_affine_loop_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_affine_loop_check P q arity positions c z env A firststeps steps u v"
  shows "\<exists>ts :: ('f,'v) term list. length ts=arity \<and>
    (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  obtain es gs C bs where atom: "lp_word_atom c z (lp_alook env) A=Some (q,es)"
    and arity: "length es=arity" and positions: "\<forall>i\<in>set positions. i<arity"
    and first: "lp_match_run P [A] firststeps=Some gs" and progress: "firststeps\<noteq>[]"
    and rest: "lp_affine_run P c z (lp_alook env) gs steps=Some (C#bs)"
    and closed: "lp_affine_closed c z (lp_alook env) A C u v"
    using ok by (auto simp: lp_affine_loop_check_def list_all_iff split: option.splits list.splits)
  let ?ts = "map (\<lambda>a. lp_word_term c z (lp_aeval a 0 0)) es"
  have bad: "\<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ?ts)]}"
  proof -
    have equal: "lp_atom_eval A (lp_aenv c z (lp_alook env) 0 0)=
        (q,map (\<lambda>t. lp_ieval t LPIVar) ?ts)"
      using lp_word_atom_sound[OF atom, of 0 0]
      by (simp add: o_def)
    show ?thesis unfolding equal[symmetric]
      by (rule lp_affine_trace_loop[OF first progress rest closed])
  qed
  show ?thesis by (rule exI[of _ ?ts]) (use arity positions bad in \<open>auto simp: nth_map\<close>)
qed

end
