theory LP_Prolog_Finite_Source_Bridges
  imports LP_Prolog_Finite_Source LP_Prolog_Context_Finite_Comparison LP_Prolog_Context_Identity
begin

lemma lpp_finite_source_nonbuiltin_base:
  assumes clear: "lpp_no_builtin_frame ss"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      (lpc_return_eval eta ss) event tt"
  shows "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  using step lpp_no_builtin_frame_sound[OF clear, of eta]
  by (cases rule: lpp_answer_transition.cases)
    (auto simp: lpp_builtin_active_def dest: lpp_finite_source_selected)

lemma lpp_finite_source_nonis_step:
  assumes different: "f\<noteq>''2:is''" and non_disequality: "f\<noteq>lpp_disequality_predicate" and nonlength: "f\<noteq>''2:length''" and nonprobe: "\<not>lpp_probe_name f" and nonsubtract: "f\<noteq>''3:subtract''" and nonbranch: "f\<noteq>''2:;''" and nonlist: "f\<noteq>''1:is_list''" and selected: "(f,length ts)\<in>lpp_builtin_signature"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#saved) event tt =
    lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#saved) event tt"
  by (rule lpp_selected_builtin_cong[OF selected]) (rule lpp_finite_source_legacy[OF different non_disequality nonlength nonprobe nonsubtract nonbranch nonlist])

lemma lpp_finite_identity_step:
  assumes name: "lpp_identity_name f"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt
    \<longleftrightarrow> event=None \<and>
      tt=(if lpp_identity_holds f a b then (LPCGoals gs,eta)#saved else saved)"
proof -
  have ne: "f\<noteq>''2:is''" using name by (auto simp: lpp_identity_name_def)
  have nd: "f\<noteq>lpp_disequality_predicate" using name by auto
  have nl: "f\<noteq>''2:length''" using name by (auto simp: lpp_identity_name_def)
  have ns: "f\<noteq>''3:subtract''" using name by (auto simp: lpp_identity_name_def)
  have nb: "f\<noteq>''2:;''" using name by (auto simp: lpp_identity_name_def)
  have nlist: "f\<noteq>''1:is_list''" using name by (auto simp: lpp_identity_name_def)
  have np: "\<not>lpp_probe_name f" using name by (auto simp only: lpp_identity_name_def lpp_nonprobe_names)
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_identity_selected[OF name] by (simp add: numeral_2_eq_2)
  show ?thesis by (simp only: lpp_finite_source_nonis_step[OF ne nd nl np ns nb nlist selected] lpp_integer_identity_step[OF name])
qed

lemma lpp_finite_source_comparison_step:
  assumes descriptor: "lpp_comparison_descriptor f comparison reversed"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
  shows "event=None \<and>
    ((tt=(LPCGoals gs,eta)#saved \<and>
      lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) (LPPBuiltinSuccess LPIVar))
     \<or> tt=saved \<or> tt=[])"
proof -
  have ne: "f\<noteq>''2:is''" using descriptor by (cases comparison; cases reversed; auto)
  have comparison: "lpp_source_comparison f=Some (comparison,reversed)"
    using descriptor by (simp only: lpp_source_comparison_descriptor)
  have nd: "f\<noteq>lpp_disequality_predicate"
  proof
    assume "f=lpp_disequality_predicate"
    with comparison show False by (simp only: lpp_disequality_names option.distinct)
  qed
  have nl: "f\<noteq>''2:length''" using comparison by auto
  have ns: "f\<noteq>''3:subtract''" using comparison by auto
  have nb: "f\<noteq>''2:;''" using comparison by auto
  have nlist: "f\<noteq>''1:is_list''" using comparison by auto
  have np: "\<not>lpp_probe_name f"
  proof
    assume name: "lpp_probe_name f"
    have none: "lpp_source_comparison f=None"
      using name by (auto simp only: lpp_probe_name_def lpp_probe_legacy_flags(3,8,13))
    with comparison show False by simp
  qed
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_comparison_selected[OF descriptor] by (simp add: numeral_2_eq_2)
  have old: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
    using step by (simp only: lpp_finite_source_nonis_step[OF ne nd nl np ns nb nlist selected])
  show ?thesis by (rule lpp_finite_comparison_step[OF descriptor old])
qed

end
