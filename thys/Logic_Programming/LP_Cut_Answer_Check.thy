theory LP_Cut_Answer_Check
  imports LP_Cut_Answer_Split LP_Cut_Control_Check LP_Cut_Output_Groundness
begin

lemma lpc_ild_prefix_SN:
  fixes Q :: "('f,string) lp_clause list"
    and xs :: "('f,string) lp_iatom list"
  assumes sn: "SN_on (lp_ild Q) {xs}"
  shows "\<forall>ps rest. xs = ps@rest \<longrightarrow> SN_on (lp_ild Q) {ps}"
proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
  fix xs ps rest
  assume ih: "\<And>ys. (xs,ys)\<in>lp_ild Q \<Longrightarrow>
    \<forall>qs rs. ys=qs@rs \<longrightarrow> SN_on (lp_ild Q) {qs}"
    and xs: "xs = ps@rest"
  show "SN_on (lp_ild Q) {ps}"
  proof (rule step_reflects_SN_on)
    fix qs assume step: "(ps,qs)\<in>lp_ild Q"
    obtain a gs c \<sigma> \<rho> where c: "c<length Q"
      and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (Q!c)) \<rho>"
      and ps: "ps=a#gs"
      and qs: "qs=map (\<lambda>b. lp_atom_eval b \<rho>) (snd (Q!c)) @
        map (\<lambda>b. lp_iatom_subst b \<sigma>) gs"
      using step by (cases rule: lp_ild.cases) blast
    have lifted: "(xs,qs @ map (\<lambda>b. lp_iatom_subst b \<sigma>) rest)\<in>lp_ild Q"
      unfolding xs ps qs
      using lp_ild.resolve[OF c eq, of "gs@rest"] by simp
    show "SN_on (lp_ild Q) {qs}" using ih[OF lifted] by blast
  qed
qed

text \<open>The residual clause preserves the answer environment by sharing
variables between the pregs and the continuation call. The child may itself
refer back to this node: strict residual reachability, not an assumed solved
child, justifies recursion. New output-groundness facts require a separately
checked recursive success-mode table; guards still require preservation.\<close>

definition lpc_check_answer_split where
  "lpc_check_answer_split P Q nds nd pregs rest Fs modes j =
    (j<length nds \<and> lpcn_state nd=[LPCGoals (pregs@rest)] \<and>
     list_all (lpc_control_goal (set Fs)) pregs \<and>
     lpc_control_program P Q (set Fs) \<and>
     lpcn_state (nds!j)=[LPCGoals rest] \<and>
     lp_ground_check Q modes \<and>
     set (lpcn_ground (nds!j)) \<subseteq>
       lp_ground_flow modes (map lpc_control_atom pregs) (set (lpcn_ground nd)) \<and>
     set (lpcn_guards (nds!j)) \<subseteq> set (filter lpc_answer_negative_guard (lpcn_guards nd)) \<and>
     ((lpcn_pred nd,map Var (lpcn_vars nd)),
       map lpc_control_atom pregs @ [(lpcn_pred (nds!j),map Var (lpcn_vars (nds!j)))])\<in>set Q)"

theorem lpc_check_answer_split_sound:
  fixes P :: "('a,string) lp_cut_program"
    and \<eta> :: "string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_answer_split P Q nds nd pregs rest Fs modes j"
    and incoming: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred nd,map \<eta> (lpcn_vars nd))]}"
    and ih: "\<And>k \<rho>. k<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!k))) (lpcn_guards (nds!k)) \<rho> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!k),map \<rho> (lpcn_vars (nds!k)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (lpcn_state (nds!k)) \<rho>}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
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
  have source: "SN_on (lp_cut_source P)
    {[LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) pregs @
       map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest)]}"
  proof (rule lpc_control_prefix_answers_SN[OF program lpc_control_eval(1)[OF domain]])
    show "SN_on (lp_ild Q) {map lpc_control_iatom (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) pregs)}"
      using ps by (simp only: lpc_control_eval(2)[OF domain])
  next
    fix \<rho> assume path: "((map lpc_control_iatom (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) pregs),\<eta>),([],\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>*"
    have answers: "((?ps,\<eta>),([],\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>*"
      using path by (simp only: lpc_control_eval(2)[OF domain])
    have suffix: "(?ps @ map (\<lambda>a. lp_atom_eval a \<eta>) ?tail,
       [(lpcn_pred ?child,map \<rho> (lpcn_vars ?child))])\<in>(lp_ild Q)\<^sup>*"
      using lp_seg_answer_steps_append[OF answers, of ?tail]
      by (simp add: lp_atom_eval_def o_def)
    have reach: "(?root,[(lpcn_pred ?child,map \<rho> (lpcn_vars ?child))])\<in>(lp_ild Q)\<^sup>+"
      using entry suffix by (meson r_into_trancl trancl_rtrancl_trancl)
    have known: "lp_cut_knowledge (set (lpcn_ground ?child)) (lpcn_guards ?child) \<rho>"
      by (rule lpc_answer_knowledge_outputs[OF modes answers incoming ground guards])
    show "SN_on (lp_cut_source P) {[LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<rho>)) rest)]}"
      using ih[OF bound known reach] by (simp add: child lp_cut_state_map_def)
  qed
  show ?thesis using source by (simp add: shape lp_cut_state_map_def)
qed

end
