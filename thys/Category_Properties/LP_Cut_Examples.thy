theory LP_Cut_Examples
  imports LP_Properties
begin

text \<open>An empty ordered program finitely fails from every query. This
checks the complete execution boundary, including clause selection and removal
of the invocation barrier, in every unification domain.\<close>
lemma logic_cut_empty_terminates: "logic_cut_terminates_in D [] p modes"
proof (unfold logic_cut_terminates_in_def, clarify)
  fix ts s
  assume query: "logic_query (LogicUser p) modes (LogicUser p,ts)"
    and initial: "s 0 = [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]"
    and steps: "\<forall>n. logic_cut_step D [] (s n) (s (Suc n))"
  have zero: "logic_cut_step D [] (s 0) (s (Suc 0))" by (rule spec[OF steps])
  obtain m where first: "s (Suc 0) = [LogicBarrier m]"
    using zero unfolding initial
    by (cases rule: logic_cut_step.cases) (auto simp: logic_slice_def)
  have one: "logic_cut_step D [] [LogicBarrier m] (s (Suc (Suc 0)))" using spec[OF steps, of "Suc 0"] by (simp add: first)
  have second: "s (Suc (Suc 0)) = []" using one by (cases rule: logic_cut_step.cases) auto
  have two: "logic_cut_step D [] [] (s (Suc (Suc (Suc 0))))" using spec[OF steps, of "Suc (Suc 0)"] by (simp add: second)
  from two show False by (cases rule: logic_cut_step.cases) auto
qed
corollary lp_cut_empty_finite: "lp_cut_finite_terminates [] p modes"
  by (simp add: lp_cut_finite_terminates_def logic_cut_empty_terminates)
corollary lp_cut_empty_rational: "lp_cut_rational_terminates [] p modes"
  by (simp add: lp_cut_rational_terminates_def logic_cut_empty_terminates)
corollary lp_cut_empty_infinite: "lp_cut_infinite_terminates [] p modes"
  by (simp add: lp_cut_infinite_terminates_def logic_cut_empty_terminates)

text \<open>Calling an unbound variable is a finite error, not a self-loop or
permission to try saved alternatives. This is independent of occurs-check.\<close>
lemma logic_unbound_meta_stuck:
  "\<not> logic_cut_step D P (LogicGoals (LogicMeta (LVar x)#gs)#es) t"
  by (auto elim: logic_cut_step.cases logic_lower_diverges.cases)

end
