theory LP_Cut_Domain_Precise_Answer_Split
  imports LP_Cut_Domain_Precise_Stack
begin

context cut_runtime_domain
begin

theorem precise_control_prefix_answers_SN:
  fixes P :: "('f,string) lp_cut_program"
    and prefix :: "('f lp_cut_symbol,string) lp_iterm lp_cut_goal list"
    and rest :: "('f lp_cut_symbol,string) term lp_cut_goal list"
    and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_igoal F) prefix"
    and sn: "SN_on (lp_ild Q) {map lpc_control_iatom prefix}"
    and continuation: "\<And>\<rho>. ((map lpc_control_iatom prefix,\<eta>),([],\<rho>))\<in>(answer_step Q)\<^sup>* \<Longrightarrow>
      SN_on (precise_source P) {[LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<rho>)) rest)]}"
  shows "SN_on (precise_source P) {[LPCGoals (prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest)]}"
proof -
  let ?eval = "\<lambda>\<rho>. map (lp_cut_map (\<lambda>t. lp_ieval t \<rho>)) rest"
  have all: "\<forall>ps :: ('f lp_cut_symbol,string) lp_iterm lp_cut_goal list.
    \<forall>\<eta> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    qs=map lpc_control_iatom ps \<longrightarrow> list_all (lpc_control_igoal F) ps \<longrightarrow>
    (\<forall>\<rho>. ((qs,\<eta>),([],\<rho>))\<in>(answer_step Q)\<^sup>* \<longrightarrow>
      SN_on (precise_source P) {[LPCGoals (?eval \<rho>)]}) \<longrightarrow>
    SN_on (precise_source P) {[LPCGoals (ps@?eval \<eta>)]}"
    if sn: "SN_on (lp_ild Q) {qs}" for qs
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix qs :: "('f lp_cut_symbol,string) lp_iatom list"
      and ps :: "('f lp_cut_symbol,string) lp_iterm lp_cut_goal list"
      and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
    assume ih: "\<And>rs. (qs,rs)\<in>lp_ild Q \<Longrightarrow>
      \<forall>bs :: ('f lp_cut_symbol,string) lp_iterm lp_cut_goal list.
      \<forall>\<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      rs=map lpc_control_iatom bs \<longrightarrow> list_all (lpc_control_igoal F) bs \<longrightarrow>
      (\<forall>\<nu>. ((rs,\<rho>),([],\<nu>))\<in>(answer_step Q)\<^sup>* \<longrightarrow>
        SN_on (precise_source P) {[LPCGoals (?eval \<nu>)]}) \<longrightarrow>
      SN_on (precise_source P) {[LPCGoals (bs@?eval \<rho>)]}"
      and qs: "qs=map lpc_control_iatom ps"
      and dom: "list_all (lpc_control_igoal F) ps"
      and returns: "\<forall>\<rho>. ((qs,\<eta>),([],\<rho>))\<in>(answer_step Q)\<^sup>* \<longrightarrow>
        SN_on (precise_source P) {[LPCGoals (?eval \<rho>)]}"
    have continue: "SN_on (precise_source P) {[LPCGoals (bs@?eval \<rho>)]}"
      if ast: "((qs,\<eta>),(map lpc_control_iatom bs,\<rho>))\<in>answer_step Q"
        and bs: "list_all (lpc_control_igoal F) bs" for bs \<rho>
    proof -
      have st: "(qs,map lpc_control_iatom bs)\<in>lp_ild Q"
        by (rule answer_step_erases[OF ast])
      have later: "\<forall>\<nu>. ((map lpc_control_iatom bs,\<rho>),([],\<nu>))\<in>(answer_step Q)\<^sup>* \<longrightarrow>
        SN_on (precise_source P) {[LPCGoals (?eval \<nu>)]}"
        using returns converse_rtrancl_into_rtrancl[OF ast] by blast
      show ?thesis using ih[OF st] bs later by blast
    qed
    show "SN_on (precise_source P) {[LPCGoals (ps@?eval \<eta>)]}"
    proof (cases ps)
      case Nil then show ?thesis using returns qs by simp
    next
      case PS: (Cons g tail)
      have tail: "list_all (lpc_control_igoal F) tail" using dom PS by simp
      have empty: "SN_on (precise_source P) {[]}"
        by (rule step_reflects_SN_on) (auto elim: precise_source.cases)
      show ?thesis
      proof (cases "\<exists>f ts. g=LPCAtom (LPIFun (LPCUser f) ts)")
        case False
        have shape: "(\<exists>m. g=LPCCut m) \<or> g=LPCTrue \<or> g=LPCFail"
          using dom PS False by (auto simp: lpc_control_igoal_iff)
        have native: "((qs,\<eta>),(map lpc_control_iatom tail,\<lambda>x. lp_isubst (\<eta> x) LPIVar))\<in>lp_seg_answer_step Q"
          using lpc_control_answer_truth[OF program, of "map lpc_control_iatom tail" \<eta>] qs PS shape by auto
        have ast: "((qs,\<eta>),(map lpc_control_iatom tail,\<eta>))\<in>answer_step Q"
          using answer_step.step[OF native] variables by simp
        have tail_sn: "SN_on (precise_source P) {[LPCGoals (tail@?eval \<eta>)]}"
          by (rule continue[OF ast tail])
        show ?thesis by (rule step_reflects_SN_on)
          (use shape PS tail_sn empty in \<open>auto elim: precise_source.cases\<close>)
      next
        case True
        obtain f ts where g: "g=LPCAtom (LPIFun (LPCUser f) ts)" and f: "f\<in>F"
          using dom PS True by (auto simp: lpc_control_igoal_iff)
        have clauses: "SN_on (precise_source P) {[LPCClause (ps@?eval \<eta>) c m]}" for c m
        proof (rule step_reflects_SN_on)
          fix s assume st: "([LPCClause (ps@?eval \<eta>) c m],s)\<in>precise_source P"
          from st show "SN_on (precise_source P) {s}"
          proof cases
            case (resolve a gs \<sigma> \<rho>)
            have a: "a=LPIFun (LPCUser f) ts" using resolve PS g by auto
            have c: "c<length P" using resolve by auto
            have eq: "lp_isubst (LPIFun (LPCUser f) ts) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
              using resolve a by (auto simp: mgu_resolve_def)
            let ?bs = "map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
              map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) tail"
            let ?post = "\<lambda>x. lp_isubst (\<eta> x) \<sigma>"
            have bs: "list_all (lpc_control_igoal F) ?bs"
              by (rule lpc_control_resolution(1)[OF program f tail c eq])
            have native: "((qs,\<eta>),(map lpc_control_iatom ?bs,?post))\<in>lp_seg_answer_step Q"
              using lpc_control_answer_resolution[OF program f tail c eq, where \<eta>=\<eta> and m=m]
              by (simp add: qs PS g)
            have ds: "\<forall>x. D (\<sigma> x)" using resolve by (auto simp: mgu_resolve_def)
            have ast: "((qs,\<eta>),(map lpc_control_iatom ?bs,?post))\<in>answer_step Q"
              by (rule answer_step.step[OF native ds])
            have child: "SN_on (precise_source P) {[LPCGoals (?bs@?eval ?post)]}"
              by (rule continue[OF ast bs])
            have shape: "s=[LPCGoals (?bs@?eval ?post)]" using resolve PS g
              by (auto simp: map_map o_def lp_cut_map_comp lp_ieval_subst)
            show ?thesis using child by (simp add: shape)
          next
            case backtrack then show ?thesis using empty by simp
          qed (use PS g in auto)
        qed
        have barrier: "SN_on (precise_source P) {[LPCBarrier m]}" for m
          by (rule precise_barriers_SN) simp
        show ?thesis
        proof (rule step_reflects_SN_on)
          fix s assume st: "([LPCGoals (ps@?eval \<eta>)],s)\<in>precise_source P"
          from st show "SN_on (precise_source P) {s}"
          proof cases
            case case_call
            show ?thesis by (rule precise_singleton_stack_SN)
              (use clauses case_call PS g barrier in auto)
          qed (use PS g in auto)
        qed
      qed
    qed
  qed
  show ?thesis using all[OF sn] domain continuation by blast
qed

theorem precise_check_answer_split_sound:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_answer_split P Q nds nd pregs rest Fs modes j"
    and incoming: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred nd,map \<eta> (lpcn_vars nd))]}"
    and ih: "\<And>\<rho>.
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<rho> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<rho> (lpcn_vars (nds!j)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      SN_on (precise_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<rho>}"
  shows "SN_on (precise_source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof -
  let ?child = "nds!j"
  let ?ps = "map (\<lambda>a. lp_atom_eval a \<eta>) (map lpc_control_atom pregs)"
  let ?tail = "[(lpcn_pred ?child,map Var (lpcn_vars ?child))]"
  let ?root = "[(lpcn_pred nd,map \<eta> (lpcn_vars nd))]"
  have bound: "j<length nds" and shape: "lpcn_state nd=[LPCGoals (pregs@rest)]"
    and domain: "list_all (lpc_control_goal (set Fs)) pregs"
    and program: "lpc_control_program P Q (set Fs)"
    and child: "lpcn_state ?child=[LPCGoals rest]"
    and modes: "lp_ground_check Q modes"
    and ground: "set (lpcn_ground ?child) \<subseteq>
      lp_ground_flow modes (map lpc_control_atom pregs) (set (lpcn_ground nd))"
    and guards: "set (lpcn_guards ?child) \<subseteq> set (filter lpc_answer_negative_guard (lpcn_guards nd))"
    and clause: "((lpcn_pred nd,map Var (lpcn_vars nd)),map lpc_control_atom pregs @ ?tail)\<in>set Q"
    using checked by (auto simp: lpc_check_answer_split_def)
  have entry: "(?root,?ps @ map (\<lambda>a. lp_atom_eval a \<eta>) ?tail)\<in>lp_ild Q"
    using lp_seg_residual_step[OF clause, of "(lpcn_pred nd,map \<eta> (lpcn_vars nd))" LPIVar \<eta> "[]"]
    by (simp add: lp_iatom_subst_def lp_atom_eval_def o_def)
  have body: "SN_on (lp_ild Q) {?ps @ map (\<lambda>a. lp_atom_eval a \<eta>) ?tail}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF residual]]) (use entry in auto)
  have ps: "SN_on (lp_ild Q) {?ps}" using lpc_ild_prefix_SN[OF body] by blast
  have source: "SN_on (precise_source P)
    {[LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) pregs @
       map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest)]}"
  proof (rule precise_control_prefix_answers_SN[OF program lpc_control_eval(1)[OF domain]])
    show "SN_on (lp_ild Q) {map lpc_control_iatom (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) pregs)}"
      using ps by (simp only: lpc_control_eval(2)[OF domain])
  next
    fix \<rho> assume path: "((map lpc_control_iatom (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) pregs),\<eta>),([],\<rho>))\<in>(answer_step Q)\<^sup>*"
    have answers: "((?ps,\<eta>),([],\<rho>))\<in>(answer_step Q)\<^sup>*"
      using path by (simp only: lpc_control_eval(2)[OF domain])
    have suffix: "(?ps @ map (\<lambda>a. lp_atom_eval a \<eta>) ?tail,
       [(lpcn_pred ?child,map \<rho> (lpcn_vars ?child))])\<in>(lp_ild Q)\<^sup>*"
      using lp_seg_answer_steps_append[OF answer_paths_native[OF answers], of ?tail]
      by (simp add: lp_atom_eval_def o_def)
    have reach: "(?root,[(lpcn_pred ?child,map \<rho> (lpcn_vars ?child))])\<in>(lp_ild Q)\<^sup>+"
      using entry suffix by (meson r_into_trancl trancl_rtrancl_trancl)
    have known: "knowledge (set (lpcn_ground ?child)) (lpcn_guards ?child) \<rho>"
      by (rule answer_outputs[OF modes answers incoming ground guards])
    show "SN_on (precise_source P) {[LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<rho>)) rest)]}"
      using ih[OF known reach] by (simp add: child lp_cut_state_map_def)
  qed
  show ?thesis using source by (simp add: shape lp_cut_state_map_def)
qed

end
end
