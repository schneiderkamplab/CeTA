theory LP_Cut_Control_Check
  imports LP_Cut_Control_Residual LP_Cut_Table_Link LP_Residual_Roles
begin

lemma lpc_control_program_code[code]:
  "lpc_control_program P Q F = (((LPCTruth,[]),[])\<in>set Q \<and> list_all (\<lambda>(h,gs). case h of
    Fun g ts \<Rightarrow> (case g of LPCUser f \<Rightarrow> (f\<notin>F \<or>
      (list_all (lpc_control_goal F) gs \<and> ((LPCUser f,ts),map lpc_control_atom gs)\<in>set Q))
      | _\<Rightarrow>True) | _\<Rightarrow>False) P)"
proof -
  have indices: "(\<forall>i<length xs. A (xs!i)) = list_all A xs" for A xs
    by (auto simp: list_all_iff in_set_conv_nth; metis nth_mem)
  have point: "(\<exists>g ts. h=Fun g ts \<and>
      (\<forall>f. g=LPCUser f \<longrightarrow> f\<in>F \<longrightarrow> list_all (lpc_control_goal F) gs \<and>
        ((LPCUser f,ts),map lpc_control_atom gs)\<in>set Q)) =
      (case h of Fun g ts \<Rightarrow> (case g of LPCUser f \<Rightarrow> (f\<notin>F \<or>
       (list_all (lpc_control_goal F) gs \<and> ((LPCUser f,ts),map lpc_control_atom gs)\<in>set Q))
       | _\<Rightarrow>True) | _\<Rightarrow>False)" for h gs
    by (cases h) (auto split: lp_cut_symbol.splits)
  show ?thesis using indices[of P "\<lambda>c. \<exists>g ts.
    fst c=Fun g ts \<and> (\<forall>f. g=LPCUser f \<longrightarrow> f\<in>F \<longrightarrow>
      list_all (lpc_control_goal F) (snd c) \<and>
      ((LPCUser f,ts),map lpc_control_atom (snd c))\<in>set Q)"]
    by (simp only: lpc_control_program_def point case_prod_unfold)
qed

definition lpc_control_extract where
  "lpc_control_extract P Fs = ((LPCTruth,[]),[]) # map (\<lambda>c.
    (lpc_control_atom (LPCAtom (fst c)),map lpc_control_atom (snd c)))
    (filter (\<lambda>c. case fst c of Fun (LPCUser f) ts \<Rightarrow> f\<in>set Fs | _\<Rightarrow>False) P)"
definition lpc_control_role where
  "lpc_control_role roles f = (case map_of roles f of None\<Rightarrow>LPCTruth | Some g\<Rightarrow>g)"
definition lpc_check_control where
  "lpc_check_control P Q nd Fs roles = (case lpcn_state nd of [LPCGoals gs]\<Rightarrow>
    list_all (lpc_control_goal (set Fs)) gs \<and>
    lpc_control_program P (lpc_control_extract P Fs) (set Fs) \<and>
    set (lp_roles_program (lpc_control_role roles) id (lpc_control_extract P Fs))  \<subseteq>  set Q \<and>
    ((lpcn_pred nd,map Var (lpcn_vars nd)),
      map (lp_roles_atom (lpc_control_role roles) id) (map lpc_control_atom gs))\<in>set Q
    | _\<Rightarrow>False)"

lemma lpc_control_ild_mono:
  fixes P Q :: "('f,'v) lp_clause list"
  assumes "set P \<subseteq> set Q"
  shows "lp_ild P \<subseteq> (lp_ild Q :: ('f,'w) lp_iatom list rel)"
proof
  fix st :: "('f,'w) lp_iatom list \<times> ('f,'w) lp_iatom list"
  assume step: "st\<in>lp_ild P"
  obtain s t where pair: "st=(s,t)" by (cases st) auto
  have "(s,t)\<in>lp_ild P" using step pair by simp
  then obtain a gs c \<sigma> \<rho> where c: "c<length P"
    and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<rho>"
    and st: "st=(a#gs,map (\<lambda>b. lp_atom_eval b \<rho>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) gs)"
    by (cases rule: lp_ild.cases) (auto simp: pair)
  have member: "P!c\<in>set Q" using c assms by auto
  have clause: "(fst (P!c),snd (P!c))\<in>set Q" using member by simp
  show "st\<in>lp_ild Q" unfolding st
    by (rule lp_seg_residual_step[OF clause eq])
qed

lemma lpc_control_eval:
  assumes "list_all (lpc_control_goal F) gs"
  shows "list_all (lpc_control_igoal F) (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) gs)"
    "map lpc_control_iatom (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) gs) =
      map (\<lambda>a. lp_atom_eval a \<eta>) (map lpc_control_atom gs)"
  using assms by (induct gs) (auto simp: lpc_control_goal_iff lp_atom_eval_def)+

theorem lpc_check_control_sound:
  fixes P :: "('a,string) lp_cut_program"
    and \<eta> :: "string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_control P Q nd Fs roles"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map \<eta> (lpcn_vars nd))]}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
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
  have source: "SN_on (lp_cut_source P)
    {[LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) gs)]}"
    by (rule lpc_control_goals_SN[OF program lpc_control_eval(1)[OF plain]])
      (use ordinary in \<open>simp only: lpc_control_eval(2)[OF plain]\<close>)
  show ?thesis using source by (simp add: state lp_cut_state_map_def)
qed

end
