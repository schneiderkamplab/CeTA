theory LP_Cut_Control_Residual
  imports LP_Cut_Plain
begin

fun lpc_control_atom where
  "lpc_control_atom (LPCAtom (Fun (LPCUser f) ts)) = (LPCUser f,ts)"
| "lpc_control_atom g = (LPCTruth,[])"
fun lpc_control_iatom where
  "lpc_control_iatom (LPCAtom (LPIFun (LPCUser f) ts)) = (LPCUser f,ts)"
| "lpc_control_iatom g = (LPCTruth,[])"
fun lpc_control_goal where
  "lpc_control_goal F (LPCAtom (Fun (LPCUser f) ts)) = (f\<in>F)"
| "lpc_control_goal F (LPCCut m) = True"
| "lpc_control_goal F LPCTrue = True"
| "lpc_control_goal F LPCFail = True"
| "lpc_control_goal F g = False"
fun lpc_control_igoal where
  "lpc_control_igoal F (LPCAtom (LPIFun (LPCUser f) ts)) = (f\<in>F)"
| "lpc_control_igoal F (LPCCut m) = True"
| "lpc_control_igoal F LPCTrue = True"
| "lpc_control_igoal F LPCFail = True"
| "lpc_control_igoal F g = False"

definition lpc_control_program where
  "lpc_control_program P Q F =
    (((LPCTruth,[]),[])\<in>set Q \<and> (\<forall>c<length P. \<exists>g ts. fst (P!c)=Fun g ts \<and>
       (\<forall>f. g=LPCUser f \<longrightarrow> f\<in>F \<longrightarrow>
        list_all (lpc_control_goal F) (snd (P!c)) \<and>
        ((LPCUser f,ts),map lpc_control_atom (snd (P!c)))\<in>set Q)))"

lemma lpc_control_goal_iff:
  "lpc_control_goal F g \<longleftrightarrow> (\<exists>f ts. g=LPCAtom (Fun (LPCUser f) ts) \<and> f\<in>F) \<or> (\<exists>m. g=LPCCut m) \<or> g=LPCTrue \<or> g=LPCFail"
  by (induct F g rule: lpc_control_goal.induct) auto
lemma lpc_control_igoal_iff:
  "lpc_control_igoal F g \<longleftrightarrow> (\<exists>f ts. g=LPCAtom (LPIFun (LPCUser f) ts) \<and> f\<in>F) \<or> (\<exists>m. g=LPCCut m) \<or> g=LPCTrue \<or> g=LPCFail"
  by (induct F g rule: lpc_control_igoal.induct) auto

lemma lpc_control_bind:
  assumes "list_all (lpc_control_goal F) gs"
  shows "list_all (lpc_control_igoal F) (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) gs)"
    "map lpc_control_iatom (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) gs) =
      map (\<lambda>a. lp_atom_eval a \<rho>) (map lpc_control_atom gs)"
  using assms
  by (induct gs) (auto simp: lp_atom_eval_def lpc_control_goal_iff)+

lemma lpc_control_subst:
  assumes "list_all (lpc_control_igoal F) gs"
  shows "list_all (lpc_control_igoal F) (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)"
    "map lpc_control_iatom (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs) =
      map (\<lambda>a. lp_iatom_subst a \<sigma>) (map lpc_control_iatom gs)"
  using assms
  by (induct gs) (auto simp: lp_iatom_subst_def lpc_control_igoal_iff)+

lemma lpc_control_resolution:
  fixes m :: nat
  assumes program: "lpc_control_program P Q F"
    and f: "f\<in>F" and tail: "list_all (lpc_control_igoal F) gs"
    and c: "c<length P" and eq: "lp_isubst (LPIFun (LPCUser f) ts) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
  defines "hs \<equiv> map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
    map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs"
  shows "list_all (lpc_control_igoal F) hs"
    "((LPCUser f,ts)#map lpc_control_iatom gs,map lpc_control_iatom hs)\<in>lp_ild Q"
proof -
  obtain g us where h: "fst (P!c)=Fun g us"
    and selected: "\<And>f. g=LPCUser f \<Longrightarrow> f\<in>F \<Longrightarrow>
      list_all (lpc_control_goal F) (snd (P!c)) \<and>
      ((LPCUser f,us),map lpc_control_atom (snd (P!c)))\<in>set Q"
    using program c unfolding lpc_control_program_def by blast
  have gf: "g=LPCUser f" using eq by (simp add: h)
  have body: "list_all (lpc_control_goal F) (snd (P!c))"
    and clause: "((LPCUser f,us),map lpc_control_atom (snd (P!c)))\<in>set Q"
    using selected f gf by auto
  show "list_all (lpc_control_igoal F) hs"
    using lpc_control_bind(1)[OF body] lpc_control_subst(1)[OF tail] by (auto simp: hs_def)
  have unifies: "lp_iatom_subst (LPCUser f,ts) \<sigma> = lp_atom_eval (LPCUser f,us) \<rho>"
    using eq by (simp add: h gf lp_iatom_subst_def lp_atom_eval_def)
  have step: "((LPCUser f,ts)#map lpc_control_iatom gs,
      map (\<lambda>a. lp_atom_eval a \<rho>) (map lpc_control_atom (snd (P!c))) @
      map (\<lambda>a. lp_iatom_subst a \<sigma>) (map lpc_control_iatom gs))\<in>lp_ild Q"
    by (rule lp_seg_residual_step[OF clause unifies])
  show "((LPCUser f,ts)#map lpc_control_iatom gs,map lpc_control_iatom hs)\<in>lp_ild Q"
    using step by (simp only: hs_def map_append lpc_control_bind(2)[OF body] lpc_control_subst(2)[OF tail])
qed

theorem lpc_control_goals_SN:
  fixes P :: "('f,string) lp_cut_program"
    and gs :: "('f lp_cut_symbol,string) lp_iterm lp_cut_goal list"
  assumes program: "lpc_control_program P Q F"
    and plain: "list_all (lpc_control_igoal F) gs"
    and sn: "SN_on (lp_ild Q) {map lpc_control_iatom gs}"
  shows "SN_on (lp_cut_source P) {[LPCGoals gs]}"
proof -
  have all: "\<forall>gs. list_all (lpc_control_igoal F) gs \<longrightarrow>
      qs=map lpc_control_iatom gs \<longrightarrow> SN_on (lp_cut_source P) {[LPCGoals gs]}"
    if sn: "SN_on (lp_ild Q) {qs}" for qs
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix qs gs
    assume ih: "\<And>rs. (qs,rs)\<in>lp_ild Q \<Longrightarrow>
      \<forall>hs. list_all (lpc_control_igoal F) hs \<longrightarrow>
       rs=map lpc_control_iatom hs \<longrightarrow> SN_on (lp_cut_source P) {[LPCGoals hs]}"
      and gs: "list_all (lpc_control_igoal F) gs" and qs: "qs=map lpc_control_iatom gs"
    show "SN_on (lp_cut_source P) {[LPCGoals gs]}"
    proof (cases gs)
      case Nil
      have empty: "SN_on (lp_cut_source P) {[]}"
        by (rule step_reflects_SN_on) (auto elim: lp_cut_source.cases)
      show ?thesis by (rule step_reflects_SN_on)
        (use empty in \<open>auto simp: Nil elim: lp_cut_source.cases\<close>)
    next
      case (Cons g tail)
      have tail: "list_all (lpc_control_igoal F) tail" using gs Cons by simp
      show ?thesis
      proof (cases "\<exists>f ts. g=LPCAtom (LPIFun (LPCUser f) ts)")
        case False
        have shape: "(\<exists>m. g=LPCCut m) \<or> g=LPCTrue \<or> g=LPCFail"
          using gs Cons False by (auto simp: lpc_control_igoal_iff)
        have truth: "((LPCTruth,[]),[])\<in>set Q"
          using program by (simp add: lpc_control_program_def)
        have step: "(qs,map lpc_control_iatom tail)\<in>lp_ild Q"
          using lp_seg_residual_step[OF truth, of "(LPCTruth,[])" LPIVar "\<lambda>_. LPIFun LPCTruth []" "map lpc_control_iatom tail"]
          shape qs Cons by (auto simp: lp_iatom_subst_def lp_atom_eval_def)
        have tail_sn: "SN_on (lp_cut_source P) {[LPCGoals tail]}"
          using ih[OF step] tail by blast
        have empty: "SN_on (lp_cut_source P) {[]}"
          by (rule step_reflects_SN_on) (auto elim: lp_cut_source.cases)
        show ?thesis by (rule step_reflects_SN_on)
          (use shape Cons tail_sn empty in \<open>auto elim: lp_cut_source.cases\<close>)
      next
        case True
      obtain f ts where g: "g=LPCAtom (LPIFun (LPCUser f) ts)" and f: "f\<in>F"
        using gs Cons True by (auto simp: lpc_control_igoal_iff)
      have barrier: "SN_on (lp_cut_source P) {[LPCBarrier m]}" for m
        by (rule lp_cut_barriers_SN) simp
      have clauses: "SN_on (lp_cut_source P) {[LPCClause gs c m]}" for c m
      proof (rule step_reflects_SN_on)
        fix s assume st: "([LPCClause gs c m],s)\<in>lp_cut_source P"
        from st show "SN_on (lp_cut_source P) {s}"
        proof cases
          case (resolve a sigma rho)
          have shape: "a=LPIFun (LPCUser f) ts"
            using resolve Cons g by auto
          have bound: "c<length P" using resolve by auto
          note facts = lpc_control_resolution[OF program f tail bound, of ts sigma rho m]
          show ?thesis using resolve facts ih qs Cons g shape by auto
        next
          case backtrack
          show ?thesis by (rule step_reflects_SN_on)
            (use backtrack in \<open>auto elim: lp_cut_source.cases\<close>)
        qed (use Cons g in auto)
      qed
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix s assume st: "([LPCGoals gs],s)\<in>lp_cut_source P"
        from st show "SN_on (lp_cut_source P) {s}"
        proof cases
          case case_call
          show ?thesis
            by (rule lpc_singleton_stack_SN)
              (use clauses case_call Cons g barrier in auto)
        qed (use Cons g in auto)
      qed
      qed
    qed
  qed
  show ?thesis using all[OF sn] plain by blast
qed

end

