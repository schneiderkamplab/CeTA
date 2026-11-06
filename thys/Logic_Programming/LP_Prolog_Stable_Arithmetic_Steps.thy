theory LP_Prolog_Stable_Arithmetic_Steps
 imports LP_Prolog_Stable_Source_Arithmetic
begin

lemma lpp_stable_comparison_step:
  assumes descriptor: "lpp_comparison_descriptor f comparison reversed"
    and step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
  shows "event=None \<and>
    ((tt=(LPCGoals gs,eta)#saved \<and>
      lpp_stable_compare_outcome operation comparison (if reversed then b else a)
        (if reversed then a else b) (LPPBuiltinSuccess LPIVar))
     \<or> (tt=saved \<and> lpp_stable_compare_outcome operation comparison
        (if reversed then b else a) (if reversed then a else b) LPPBuiltinFailure)
     \<or> (tt=[] \<and> lpp_stable_compare_outcome operation comparison
        (if reversed then b else a) (if reversed then a else b) LPPBuiltinError))"
proof -
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_comparison_selected[OF descriptor] by (simp add: numeral_2_eq_2)
  have outcomes: "\<And>outcome. lpp_stable_source_builtin operation f [a,b] outcome =
      lpp_stable_compare_outcome operation comparison (if reversed then b else a) (if reversed then a else b) outcome"
    by (rule lpp_stable_source_comparison[OF descriptor])
  show ?thesis using step selected
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def outcomes lpp_stable_compare_outcome_def split: if_splits)
qed

lemma lpp_stable_is_step:
  assumes step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
      ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  shows "event=None \<and>
    ((\<exists>mu. lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu) \<and>
       tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs),
           \<lambda>x. lp_isubst (eta x) mu)#saved)
     \<or> (tt=saved \<and> lpp_stable_is_outcome operation a e LPPBuiltinFailure)
     \<or> (tt=[] \<and> lpp_stable_is_outcome operation a e LPPBuiltinError))"
proof -
  have selected: "(''2:is'',length [a,e])\<in>lpp_builtin_signature" by code_simp
  have no_probe: "\<And>probe keep. \<not>lpp_stable_is_outcome operation a e (LPPBuiltinProbe probe keep)"
    by (auto simp: lpp_stable_source_is lpp_stable_is_outcome_def split: option.splits)
  show ?thesis using step selected
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def no_probe lpp_stable_source_is)
qed

ML \<open>
val checked = [@{thm lpp_stable_comparison_step}, @{thm lpp_stable_is_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable arithmetic step dependency" else ();
\<close>
end
