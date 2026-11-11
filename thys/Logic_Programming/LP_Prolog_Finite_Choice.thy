theory LP_Prolog_Finite_Choice
 imports LP_Prolog_Finite_Source
begin

definition lpp_choice_source_left where
  "lpp_choice_source_left a = (case a of Fun f ts \<Rightarrow>
    f\<noteq>LPCUser ''2:->'' \<or> length ts\<noteq>2 | _ \<Rightarrow> False)"

lemma lpp_choice_source_left_sound:
  "lpp_choice_source_left a \<Longrightarrow> lpp_choice_left (lp_ieval a eta)"
  by (cases a) (auto simp: lpp_choice_source_left_def)

lemma lpp_finite_choice_step:
  assumes choice: "lpp_choice_left a"
    and lower: "lpp_branch_lower a left" "lpp_branch_lower b right"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:;'') [a,b])#gs),active)#saved) event tt"
  shows "event=None \<and>
    tt=(LPCGoals (left@gs),active)#(LPCGoals (right@gs),active)#saved"
proof -
  have outcome: "\<And>out. lpp_finite_source_builtin ''2:;'' [a,b] out =
      (out=LPPBuiltinChoice left right)"
    using choice lower lpp_branch_lower_unique
    by (auto simp: lpp_finite_source_builtin_def lpp_disequality_predicate_def lpp_branch_outcome_def)
  show ?thesis using step
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def lpp_builtin_signature_def outcome)
qed

lemma lpp_finite_choice_domain:
  "lpp_choice_source_left a \<Longrightarrow> lpp_branch_lower_term a=Some left \<Longrightarrow>
   lpp_branch_lower_term b=Some right \<Longrightarrow>
    lpp_finite_source_domain ''2:;'' [lp_ieval a eta,lp_ieval b eta]"
  using lpp_branch_lower_term_sound[of a left eta] lpp_branch_lower_term_sound[of b right eta]
    lpp_choice_source_left_sound[of a eta]
  by (auto simp: lpp_finite_source_domain_def lpp_disequality_predicate_def lpp_branch_domain_def lpp_branch_outcome_def; blast)

ML \<open>
val checked = [@{thm lpp_finite_choice_step}, @{thm lpp_finite_choice_domain}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted choice coverage" else ();
\<close>
end
