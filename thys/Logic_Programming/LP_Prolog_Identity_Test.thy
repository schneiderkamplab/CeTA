theory LP_Prolog_Identity_Test
  imports LP_Prolog_Var_Test
begin

definition lpp_identity_name where
  "lpp_identity_name f = (f=''2:=='' \<or> f=(map char_of_nat [50,58,92,61,61]))"

definition lpp_identity_holds where
  "lpp_identity_holds f a b = (if f=''2:=='' then a=b else a\<noteq>b)"

definition lpp_test_builtin where
  "lpp_test_builtin f ts result = (lpp_var_builtin f ts result \<or>
    (lpp_identity_name f \<and> (\<exists>a b. ts=[a,b] \<and>
      result=(if lpp_identity_holds f a b then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure))))"

lemma lpp_identity_selected:
  "lpp_identity_name f \<Longrightarrow> (f,2)\<in>lpp_builtin_signature"
  by (auto simp: lpp_identity_name_def lpp_builtin_signature_def)

lemma lpp_test_builtin_selected:
  assumes "lpp_test_builtin f ts result"
  shows "(f,length ts)\<in>lpp_builtin_signature"
proof -
  from assms consider (var) "lpp_var_builtin f ts result"
    | (identity) "lpp_identity_name f" "length ts=2"
    by (auto simp: lpp_test_builtin_def)
  then show ?thesis
  proof cases
    case var then show ?thesis by (rule lpp_var_builtin_selected)
  next
    case identity
    have "(f,2)\<in>lpp_builtin_signature" by (rule lpp_identity_selected[OF identity(1)])
    then show ?thesis by (simp only: identity(2))
  qed
qed

lemma lpp_selected_builtin_cong:
  assumes selected: "(f,length ts)\<in>B"
    and same: "\<And>r. U f ts r = V f ts r"
  shows "lpp_answer_transition P B U ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es) event tt =
    lpp_answer_transition P B V ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es) event tt"
  by (rule iffI; erule lpp_answer_transition.cases)
    (use selected same in \<open>auto simp: lpp_builtin_active_def intro: lpp_answer_transition.intros\<close>)

lemma lpp_test_var_step:
  assumes name: "lpp_var_name f"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a])#gs),eta)#es) event tt =
    lpp_answer_transition P lpp_builtin_signature lpp_var_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a])#gs),eta)#es) event tt"
  by (rule lpp_selected_builtin_cong)
    (use name lpp_var_selected in \<open>auto simp: lpp_test_builtin_def\<close>)

lemma lpp_test_var_node_sound:
  assumes checked: "lpp_check_var_node fuel Q nds states nd ss f a gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin
      (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and> event=None"
proof -
  have name: "lpp_var_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
    using checked by (auto simp: lpp_check_var_node_def)
  have old: "lpp_answer_transition P lpp_builtin_signature lpp_var_builtin (lpc_return_eval eta ss) event tt"
    using step by (simp add: shape lpc_return_eval_def lpp_test_var_step[OF name])
  show ?thesis by (rule lpp_var_node_sound[OF checked known old])
qed

lemma lpp_identity_step_exact:
  assumes name: "lpp_identity_name f"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#es) event tt
    \<longleftrightarrow> event=None \<and>
      tt=(if lpp_identity_holds f a b then (LPCGoals gs,eta)#es else es)"
proof -
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_identity_selected[OF name] by (simp add: numeral_2_eq_2)
  show ?thesis
  proof (cases "lpp_identity_holds f a b")
  case True
  have outcome: "\<And>r. lpp_test_builtin f [a,b] r \<longleftrightarrow> r=LPPBuiltinSuccess LPIVar"
    using name True by (simp add: lpp_test_builtin_def lpp_var_builtin_def)
  show ?thesis using lpp_builtin_success_only[where ts="[a,b]" and f=f and sigma=LPIVar and U=lpp_test_builtin and B=lpp_builtin_signature and P=P and gs=gs and eta=eta and es=es and event=event and tt=tt, OF selected outcome] True
    by simp
next
  case False
  have outcome: "\<And>r. lpp_test_builtin f [a,b] r \<longleftrightarrow> r=LPPBuiltinFailure"
    using name False by (simp add: lpp_test_builtin_def lpp_var_builtin_def)
  show ?thesis using lpp_builtin_failure_only[where ts="[a,b]" and f=f and U=lpp_test_builtin and B=lpp_builtin_signature and P=P and gs=gs and eta=eta and es=es and event=event and tt=tt, OF selected outcome] False
    by simp
  qed
qed

definition lpp_identity_outcomes where
  "lpp_identity_outcomes f a b = (if a=b then [f=''2:==''] else [False,True])"

definition lpp_check_identity_node where
  "lpp_check_identity_node fuel Q nds states nd ss f a b gs active saved yes no =
    (lpp_identity_name f \<and> ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved \<and>
     list_all (\<lambda>holds. lpc_check_return_table_link fuel Q nds states nd
       (if holds then (LPCGoals gs,active)#saved else saved)
       (lpcn_ground nd) (lpcn_guards nd)
       (if holds=(f=''2:=='') then [(a,b)] else []) (if holds then yes else no))
       (lpp_identity_outcomes f a b))"

theorem lpp_identity_node_sound:
  assumes checked: "lpp_check_identity_node fuel Q nds states nd ss f a b gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and> event=None"
proof -
  let ?holds = "lpp_identity_holds f (lp_ieval a eta) (lp_ieval b eta)"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  let ?eqs = "if ?holds=(f=''2:=='') then [(a,b)] else []"
  have name: "lpp_identity_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    using checked by (auto simp: lpp_check_identity_node_def)
  have coverage: "?holds\<in>set (lpp_identity_outcomes f a b)"
    by (auto simp: lpp_identity_outcomes_def lpp_identity_holds_def)
  have eqs: "lp_equations ?eqs eta"
    using name by (auto simp: lp_equations_def lpp_identity_holds_def)
  have link: "lpc_check_return_table_link fuel Q nds states nd ?next
    (lpcn_ground nd) (lpcn_guards nd) ?eqs (if ?holds then yes else no)"
    using checked coverage by (auto simp: lpp_check_identity_node_def list_all_iff)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_identity_step_exact[OF name] split: if_splits)
  show ?thesis using lpc_return_table_link_sound[OF link eqs refl known] actual by auto
qed

lemma lpp_test_nonbuiltin_answer_base:
  assumes clear: "lpp_no_builtin_frame ss"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin
      (lpc_return_eval eta ss) event tt"
  shows "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  using step lpp_no_builtin_frame_sound[OF clear, of eta]
  by (cases rule: lpp_answer_transition.cases)
    (auto simp: lpp_builtin_active_def dest: lpp_test_builtin_selected)

end
