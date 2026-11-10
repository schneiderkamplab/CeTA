theory LP_Cut_Domain_Control
  imports LP_Cut_Domain_Nodes
begin

context cut_runtime_domain
begin

theorem control_goals_SN:
  fixes P :: "('f,string) lp_cut_program"
    and gs :: "('f lp_cut_symbol,string) lp_iterm lp_cut_goal list"
  assumes program: "lpc_control_program P Q F"
    and plain: "list_all (lpc_control_igoal F) gs"
    and sn: "SN_on (lp_ild Q) {map lpc_control_iatom gs}"
  shows "SN_on (source P) {[LPCGoals gs]}"
proof -
  have all: "\<forall>gs. list_all (lpc_control_igoal F) gs \<longrightarrow>
      qs=map lpc_control_iatom gs \<longrightarrow> SN_on (source P) {[LPCGoals gs]}"
    if sn: "SN_on (lp_ild Q) {qs}" for qs
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix qs gs
    assume ih: "\<And>rs. (qs,rs)\<in>lp_ild Q \<Longrightarrow>
      \<forall>hs. list_all (lpc_control_igoal F) hs \<longrightarrow>
       rs=map lpc_control_iatom hs \<longrightarrow> SN_on (source P) {[LPCGoals hs]}"
      and gs: "list_all (lpc_control_igoal F) gs" and qs: "qs=map lpc_control_iatom gs"
    show "SN_on (source P) {[LPCGoals gs]}"
    proof (cases gs)
      case Nil
      have empty: "SN_on (source P) {[]}"
        by (rule step_reflects_SN_on) (auto elim: source.cases)
      show ?thesis by (rule step_reflects_SN_on)
        (use empty in \<open>auto simp: Nil elim: source.cases\<close>)
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
        have tail_sn: "SN_on (source P) {[LPCGoals tail]}"
          using ih[OF step] tail by blast
        have empty: "SN_on (source P) {[]}"
          by (rule step_reflects_SN_on) (auto elim: source.cases)
        show ?thesis by (rule step_reflects_SN_on)
          (use shape Cons tail_sn empty in \<open>auto elim: source.cases\<close>)
      next
        case True
      obtain f ts where g: "g=LPCAtom (LPIFun (LPCUser f) ts)" and f: "f\<in>F"
        using gs Cons True by (auto simp: lpc_control_igoal_iff)
      have barrier: "SN_on (source P) {[LPCBarrier m]}" for m
        by (rule barriers_SN) simp
      have clauses: "SN_on (source P) {[LPCClause gs c m]}" for c m
      proof (rule step_reflects_SN_on)
        fix s assume st: "([LPCClause gs c m],s)\<in>source P"
        from st show "SN_on (source P) {s}"
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
            (use backtrack in \<open>auto elim: source.cases\<close>)
        qed (use Cons g in auto)
      qed
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix s assume st: "([LPCGoals gs],s)\<in>source P"
        from st show "SN_on (source P) {s}"
        proof cases
          case case_call
          show ?thesis
            by (rule singleton_stack_SN)
              (use clauses case_call Cons g barrier in auto)
        qed (use Cons g in auto)
      qed
      qed
    qed
  qed
  show ?thesis using all[OF sn] plain by blast
qed
theorem check_control_sound:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_control P Q nd Fs roles"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map \<eta> (lpcn_vars nd))]}"
  shows "SN_on (source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof -
  obtain gs where state: "lpcn_state nd=[LPCGoals gs]"
    and plain: "list_all (lpc_control_goal (set Fs)) gs"
    and program: "lpc_control_program P (lpc_control_extract P Fs) (set Fs)"
    and subset: "set (lp_roles_program (lpc_control_role roles) id (lpc_control_extract P Fs)) \<subseteq> set Q"
    and clause: "((lpcn_pred nd,map Var (lpcn_vars nd)),
      map (lp_roles_atom (lpc_control_role roles) id) (map lpc_control_atom gs))\<in>set Q"
    using checked by (auto simp: lpc_check_control_def split: list.splits lp_cut_entry.splits;
      metis list.exhaust)
  let ?body = "map (\<lambda>a. lp_atom_eval a \<eta>)
    (map (lp_roles_atom (lpc_control_role roles) id) (map lpc_control_atom gs))"
  have step: "([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],?body)\<in>lp_ild Q"
    using lp_seg_residual_step[OF clause, of "(lpcn_pred nd,map \<eta> (lpcn_vars nd))" LPIVar \<eta> "[]"]
    by (simp add: lp_iatom_subst_def lp_atom_eval_def o_def)
  have body_sn: "SN_on (lp_ild Q) {?body}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use step in auto)
  have restricted: "SN_on (lp_ild (lp_roles_program (lpc_control_role roles) id (lpc_control_extract P Fs))) {?body}"
    by (rule SN_on_subset1[OF body_sn lpc_control_ild_mono[OF subset]])
  have ordinary: "SN_on (lp_ild (lpc_control_extract P Fs))
    {map (\<lambda>a. lp_atom_eval a \<eta>) (map lpc_control_atom gs)}"
    by (rule lp_roles_termination_reflect[where p="lpc_control_role roles" and d=id])
      (use restricted in \<open>simp add: map_map o_def lp_roles_eval lp_iterm.map_id\<close>)
  have source: "SN_on (source P)
    {[LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) gs)]}"
    by (rule control_goals_SN[OF program lpc_control_eval(1)[OF plain]])
      (use ordinary in \<open>simp only: lpc_control_eval(2)[OF plain]\<close>)
  show ?thesis using source by (simp add: state lp_cut_state_map_def)
qed

end
end
