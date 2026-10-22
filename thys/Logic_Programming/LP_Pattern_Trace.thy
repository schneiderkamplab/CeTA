theory LP_Pattern_Trace
  imports LP_Success_Pattern_Check
begin

datatype ('f,'v) lp_pattern_step =
    LPPatternResolve "(nat \<times> ('f,'v) substL) list"
  | LPPatternSuccess "('f,'v) substL" "('f,'v) substL"
      "(nat \<times> ('f,'v) substL) list" "(nat \<times> ('f,'v) substL) list"

fun lp_pattern_run where
  "lp_pattern_run P sig mu gs [] = Some gs"
| "lp_pattern_run P sig mu gs (LPPatternResolve steps#rest) =
    (case lp_match_run P gs steps of None \<Rightarrow> None
     | Some hs \<Rightarrow> lp_pattern_run P sig mu hs rest)"
| "lp_pattern_run P sig mu gs (LPPatternSuccess tsb nu basetrace steps#rest) =
    (case gs of [] \<Rightarrow> None | a#tail \<Rightarrow>
      if lp_success_pattern_check P a sig tsb mu nu basetrace steps
      then lp_pattern_run P sig mu tail rest else None)"

theorem lp_pattern_run_sound:
  fixes n :: nat and r :: "'v \<Rightarrow> ('f,'w) lp_iterm"
    and P :: "('f,'v) lp_clause list"
  assumes run: "lp_pattern_run P sig mu gs steps = Some hs"
  defines "env \<equiv> (lp_pattern_env (mk_subst Var sig)^^n)
    (lp_pattern_env (mk_subst Var mu) r)"
  shows "(map (\<lambda>a. lp_atom_eval a env) gs @ tail,
      map (\<lambda>a. lp_atom_eval a env) hs @ tail)\<in>(lp_ild P)\<^sup>*"
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
    show ?thesis by (rule rtrancl_trans[OF lp_match_run_sound[OF first] Cons.hyps[OF remaining]])
  next
    case (LPPatternSuccess tsb nu basetrace trace)
    obtain a more where gs: "gs=a#more"
      and checked: "lp_success_pattern_check P a sig tsb mu nu basetrace trace"
      and remaining: "lp_pattern_run P sig mu more rest=Some hs"
      using Cons.prems by (auto simp: LPPatternSuccess split: list.splits if_splits)
    have first: "(map (\<lambda>a. lp_atom_eval a env) gs @ tail,
        map (\<lambda>a. lp_atom_eval a env) more @ tail)\<in>(lp_ild P)\<^sup>*"
      using lp_success_pattern_check_sound[OF checked, of n r
          "map (\<lambda>a. lp_atom_eval a env) more @ tail"]
      by (simp add: gs env_def)
    show ?thesis by (rule rtrancl_trans[OF first Cons.hyps[OF remaining]])
  qed
qed

theorem lp_pattern_trace_loop:
  fixes P :: "('f,'v) lp_clause list" and r :: "'v \<Rightarrow> ('f,'w) lp_iterm"
  assumes first: "lp_match_run P [A] initial_steps=Some gs"
    and progress: "initial_steps\<noteq>[]"
    and rest: "lp_pattern_run P sig mu gs steps=Some (lp_atom_subst A (mk_subst Var sig)#bs)"
  shows "\<not>SN_on (lp_ild P) {[lp_atom_eval (lp_atom_subst A (mk_subst Var mu)) r]}"
proof -
  let ?E = "\<lambda>n. (lp_pattern_env (mk_subst Var sig)^^n) (lp_pattern_env (mk_subst Var mu) r)"
  let ?F = "\<lambda>n. lp_atom_eval A (?E n)"
  let ?X = "{qs. \<exists>n tail. qs=?F n#tail}"
  have bad: "\<not>SN_on ((lp_ild P)\<^sup>+) {[?F 0]}"
  proof (rule lp_serial_not_SN[where X="?X"])
    show "[?F 0]\<in>?X" by blast
  next
    fix qs assume "qs\<in>?X"
    then obtain n tail where qs: "qs=?F n#tail" by blast
    have first': "(qs,map (\<lambda>a. lp_atom_eval a (?E n)) gs @ tail)\<in>(lp_ild P)\<^sup>+"
      using lp_match_run_nonempty_sound[OF first progress, of "?E n" tail]
      by (simp add: qs)
    have rest': "(map (\<lambda>a. lp_atom_eval a (?E n)) gs @ tail,
        ?F (Suc n)#(map (\<lambda>a. lp_atom_eval a (?E n)) bs @ tail))\<in>(lp_ild P)\<^sup>*"
      using lp_pattern_run_sound[OF rest, of n r tail]
      by (simp add: lp_atom_eval_finite_subst lp_pattern_env_def funpow_Suc_right)
    have path: "(qs,?F (Suc n)#(map (\<lambda>a. lp_atom_eval a (?E n)) bs @ tail))\<in>(lp_ild P)\<^sup>+"
      by (rule trancl_rtrancl_trancl[OF first' rest'])
    show "\<exists>t\<in>?X. (qs,t)\<in>(lp_ild P)\<^sup>+" using path by blast
  qed
  show ?thesis using bad SN_on_trancl
    by (auto simp: lp_atom_eval_finite_subst lp_pattern_env_def)
qed

definition lp_pattern_loop_check where
  "lp_pattern_loop_check P q arity positions A sig mu firststeps steps =
    (let initial=lp_atom_subst A (mk_subst Var mu) in
      fst initial=q \<and> length (snd initial)=arity \<and>
      list_all (\<lambda>i. i<arity \<and> ground (snd initial!i)) positions \<and>
      firststeps\<noteq>[] \<and>
      (case lp_match_run P [A] firststeps of None \<Rightarrow> False | Some gs \<Rightarrow>
        (case lp_pattern_run P sig mu gs steps of Some (b#bs) \<Rightarrow>
          b=lp_atom_subst A (mk_subst Var sig) | _ \<Rightarrow> False)))"

theorem lp_pattern_loop_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_pattern_loop_check P q arity positions A sig mu firststeps steps"
  shows "\<exists>ts :: ('f,'v) term list. length ts=arity \<and>
    (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  let ?initial = "lp_atom_subst A (mk_subst Var mu)"
  have query: "fst ?initial=q" "length (snd ?initial)=arity"
      "\<forall>i\<in>set positions. i<arity \<and> ground (snd ?initial!i)"
    and progress: "firststeps\<noteq>[]"
    using ok by (auto simp: lp_pattern_loop_check_def Let_def list_all_iff)
  obtain gs bs where first: "lp_match_run P [A] firststeps=Some gs"
    and rest: "lp_pattern_run P sig mu gs steps=Some (lp_atom_subst A (mk_subst Var sig)#bs)"
    using ok by (auto simp: lp_pattern_loop_check_def Let_def split: option.splits list.splits)
  have bad: "\<not>SN_on (lp_ild P) {[lp_atom_eval ?initial LPIVar]}"
    by (rule lp_pattern_trace_loop[OF first progress rest])
  show ?thesis by (rule exI[of _ "snd ?initial"])
    (use query bad in \<open>simp add: lp_atom_eval_def\<close>)
qed

end
