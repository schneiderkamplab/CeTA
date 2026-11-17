theory LP_Prolog_Separation_Head_Tests
 imports LP_Prolog_Separation_Unification_Check
begin

lemma lpp_separation_matching_positive:
 "lpp_check_separation_head [(Fun f [],body)] nd ctx (Fun f []) 0 (LPPSMatching [])"
 by (simp add: lp_cut_check_match_def)

lemma lpp_separation_matching_changed_call_rejected:
 "f\<noteq>g \<Longrightarrow>
  \<not>lpp_check_separation_head [(Fun f [],body)] nd ctx (Fun g []) 0 (LPPSMatching [])"
 by (simp add: lp_cut_check_match_def)

lemma lpp_separation_anchored_positive:
 "''input''\<in>set (lpcn_ground nd) \<Longrightarrow>
  lpp_check_separation_head [(Fun f [Var ''shared'',Var ''shared''],body)] nd ctx
   (Fun f [Var ''input'',Var ''output'']) 0
   (LPPSAnchored f [Var ''input'',Var ''output''] [Var ''shared'',Var ''shared''] [''input''])"
 by (simp add: lpp_check_anchored_head_def)

lemma lpp_separation_anchored_missing_ground_rejected:
 "''input''\<notin>set (lpcn_ground nd)\<union>lpp_source_context_ground ctx \<Longrightarrow>
  \<not>lpp_check_separation_head [(Fun f [Var ''shared'',Var ''shared''],body)] nd ctx
   (Fun f [Var ''input'',Var ''output'']) 0
   (LPPSAnchored f [Var ''input'',Var ''output''] [Var ''shared'',Var ''shared''] [''input''])"
 by simp

lemma lpp_separation_anchored_changed_head_rejected:
 "fst (P!c)\<noteq>Fun f hs \<Longrightarrow>
  \<not>lpp_check_separation_head P nd ctx a c (LPPSAnchored f actuals hs G)"
 by simp

lemma lpp_separation_spine_positive:
 "LPPOShape lpp_spine_grammar (LPReturnShape 0) arg\<in>set (snd (snd ctx)) \<Longrightarrow>
  lpp_check_separation_head
   [(Fun f [Fun (LPCUser ''2:prolog_data_2e'') [Var ''head'',Var ''tail''],Var ''counter'',Var ''out''],body)]
   nd ctx (Fun f [arg,n,m]) 0
   (LPPSSpine f arg [n,m] ''head'' ''tail'' [''counter'',''out''])"
 by simp

lemma lpp_separation_spine_changed_call_rejected:
 "a\<noteq>Fun f (arg#actuals) \<Longrightarrow>
  \<not>lpp_check_separation_head P nd ctx a c (LPPSSpine f arg actuals x y H)"
 by simp

lemma lpp_separation_spine_repeated_output_rejected:
 "x\<in>set H \<Longrightarrow>
  \<not>lpp_check_separation_head P nd ctx a c (LPPSSpine f arg actuals x y H)"
 by simp

lemma lpp_separation_unification_ground_side_positive:
 "lpcl_target yes=0 \<Longrightarrow> lpcl_target no=0 \<Longrightarrow>
  lpp_check_separation_unification P nd ctx [[]]
   (LPPFCut (LPCREquality a (Fun f []) gs active saved k l next mode outputs yes no) fs ns) None"
 by (simp add: lpp_empty_separation_branches_def lpp_empty_separation_target_def)

lemma lpp_separation_unification_nonempty_success_rejected:
 "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> separation_contexts!lpcl_target yes\<noteq>[] \<Longrightarrow>
  \<not>lpp_check_separation_unification P nd ctx separation_contexts
   (LPPFCut (LPCREquality a b gs active saved k l next mode outputs yes no) fs ns) witness"
 by (simp add: lpp_empty_separation_branches_def lpp_empty_separation_target_def)

ML \<open>
val checked = @{thms lpp_separation_matching_positive lpp_separation_matching_changed_call_rejected
 lpp_separation_anchored_positive lpp_separation_anchored_missing_ground_rejected
 lpp_separation_anchored_changed_head_rejected lpp_separation_spine_positive
 lpp_separation_spine_changed_call_rejected lpp_separation_spine_repeated_output_rejected
 lpp_separation_unification_ground_side_positive lpp_separation_unification_nonempty_success_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation head regressions" else ();
\<close>
end
