theory LP_Prolog_Stable_Legacy_Context
 imports LP_Prolog_Stable_Primitive
begin

lemma lpp_success_guard_evaluation_mono:
  assumes extends: "\<And>e t. E e t \<Longrightarrow> F e t"
    and held: "lpp_success_guard_holds E eta input_guard"
  shows "lpp_success_guard_holds F eta input_guard"
  using held by (cases input_guard) (auto intro: extends)

lemma lpp_guarded_success_evaluation_mono:
  assumes extends: "\<And>e t. E e t \<Longrightarrow> F e t"
    and success: "lpp_guarded_success P E call_atom"
  shows "lpp_guarded_success P F call_atom"
  using success
proof (induction rule: lpp_guarded_success.induct)
  case (clause h bs gs eta)
  have guards: "list_all (lpp_success_guard_holds F eta) gs"
  proof (unfold list_all_iff, intro ballI)
    fix g assume member: "g\<in>set gs"
    have held: "lpp_success_guard_holds E eta g"
      using clause.hyps member by (simp add: list_all_iff)
    show "lpp_success_guard_holds F eta g"
      using held by (cases g) (auto intro: extends)
  qed
  have children: "list_all (lpp_guarded_success P F) (map (\<lambda>b. lpp_success_atom_eval b eta) bs)"
    using clause.IH by (auto simp: list_all_iff)
  show ?case by (rule lpp_guarded_success.clause[OF clause.hyps(1) guards children])
qed

lemma lpp_evaluation_context_mono:
  assumes extends: "\<And>e t. E e t \<Longrightarrow> F e t"
    and held: "lpp_evaluation_context_holds E P ctx eta"
  shows "lpp_evaluation_context_holds F P ctx eta"
proof -
  have observation: "lpp_evaluation_observation_holds E eta obs \<Longrightarrow>
    lpp_evaluation_observation_holds F eta obs" for obs
    by (cases obs) (auto intro: extends)
  show ?thesis using held
    by (cases ctx) (auto simp: lpp_evaluation_context_holds_def list_all_iff
      intro: observation lpp_guarded_success_evaluation_mono[OF extends]
        lpp_success_guard_evaluation_mono[OF extends])
qed

lemma lpp_stable_context_finite_envelope:
  assumes compatible: "lpp_stable_integer_operations operation"
    and held: "lpp_stable_context_holds operation P ctx eta"
  shows "lpp_evaluation_context_holds lpp_finite_evaluation_result P ctx eta"
proof -
  have prior: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) P ctx eta"
    using held by (simp add: lpp_stable_context_holds_def)
  show ?thesis by (rule lpp_evaluation_context_mono[OF _ prior])
    (rule lpp_stable_evaluation_finite_envelope[OF compatible])
qed

ML \<open>
val checked = [@{thm lpp_guarded_success_evaluation_mono}, @{thm lpp_evaluation_context_mono},
  @{thm lpp_stable_context_finite_envelope}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable legacy-context dependency" else ();
\<close>
end
