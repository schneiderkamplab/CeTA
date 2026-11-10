theory LP_Prolog_Finite_Branch
 imports LP_Prolog_Finite_Source
begin

lemma lpp_finite_branch_step:
  assumes lower: "lpp_branch_lower c cs" "lpp_branch_lower y ys" "lpp_branch_lower z zs"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:;'') [LPIFun (LPCUser ''2:->'') [c,y],z])#gs),active)#saved) event tt"
  shows "event=None \<and> (\<exists>m n.
    lp_cut_fresh m (LPCGoals gs#map fst saved) \<and>
    lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved) \<and>
    tt=lpp_branch_stack cs ys zs m n gs active saved)"
proof -
  have outcome: "\<And>out. lpp_finite_source_builtin ''2:;'' [LPIFun (LPCUser ''2:->'') [c,y],z] out =
      (out=LPPBuiltinBranch cs ys zs)"
    using lower lpp_branch_lower_unique
    by (auto simp: lpp_finite_source_builtin_def lpp_disequality_predicate_def lpp_branch_outcome_def)
  show ?thesis using step
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def lpp_builtin_signature_def outcome lpp_branch_stack_def lp_cut_fresh_def)
qed

lemma lpp_finite_branch_domain:
  "lpp_branch_lower_term c=Some cs \<Longrightarrow> lpp_branch_lower_term y=Some ys \<Longrightarrow>
   lpp_branch_lower_term z=Some zs \<Longrightarrow>
    lpp_finite_source_domain ''2:;'' [lp_ieval (Fun (LPCUser ''2:->'') [c,y]) eta,lp_ieval z eta]"
  using lpp_branch_lower_term_sound[of c cs eta] lpp_branch_lower_term_sound[of y ys eta]
    lpp_branch_lower_term_sound[of z zs eta]
  by (auto simp: lpp_finite_source_domain_def lpp_disequality_predicate_def lpp_branch_domain_def lpp_branch_outcome_def)

end
