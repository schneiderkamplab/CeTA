theory TRS_Equational_Examples
  imports TRS_Equational_Spec TRS_Standard_Examples
begin
lemma equational_empty_terminates: "trs_equational_terminates A {} FA FC"
  by (simp add: trs_equational_terminates_def no_infinite_steps_def equational_step_def standard_step_def)
lemma equational_plug_count:
  "function_count s = function_count t \<Longrightarrow>
    function_count (standard_plug C s) = function_count (standard_plug C t)"
  by (induct C) auto
lemma equations_preserve_count:
  "standard_step A (equational_axioms FA FC) s t \<Longrightarrow> function_count s = function_count t"
  by (auto simp: standard_step_def equational_axioms_def intro!: equational_plug_count simp: add.assoc)
lemma conversion_preserves_count:
  "equational_conversion A FA FC s t \<Longrightarrow> function_count s = function_count t"
  unfolding equational_conversion_def
  by (induct rule: finite_steps.induct) (auto dest: equations_preserve_count)
lemma equational_reduction_decreases:
  "equational_step A {(SFun f [SVar (0::nat)],SVar 0)} FA FC s t \<Longrightarrow>
    function_count t < function_count s"
  unfolding equational_step_def
  by (metis conversion_preserves_count reduction_decreases)
lemma equational_reduction_terminates:
  "trs_equational_terminates A {(SFun f [SVar (0::nat)],SVar 0)} FA FC"
proof (rule ccontr)
  assume "\<not> trs_equational_terminates A {(SFun f [SVar (0::nat)],SVar 0)} FA FC"
  then obtain ts where steps: "\<forall>i. equational_step A {(SFun f [SVar (0::nat)],SVar 0)} FA FC (ts i) (ts (Suc i))"
    by (simp add: trs_equational_nontermination_iff) blast
  have bound: "function_count (ts n) + n \<le> function_count (ts 0)" for n
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have "function_count (ts (Suc n)) < function_count (ts n)"
      by (rule equational_reduction_decreases[OF steps[rule_format]])
    then show ?case using Suc by arith
  qed
  show False using bound[of "Suc (function_count (ts 0))"] by simp
qed

text \<open>A binary signature needs no constants. Commutativity changes an
open term below the root, and can close a rewrite step into a self-loop.\<close>
definition eq_binary :: "unit ranked_signature" where "eq_binary f = Some 2"
lemma equational_arity_mismatch:
  "\<not> arity_correct eq_binary (SFun () [])"
  "\<not> arity_correct eq_binary (SFun () [SVar (0::nat)])"
  by (simp_all add: eq_binary_def)
lemma equational_open_term: "arity_correct eq_binary (SFun () [SVar (0::nat),SVar 1])"
  by (simp add: eq_binary_def)
lemma equational_equation_step:
  "standard_step eq_binary (equational_axioms {} {()})
    (SFun () [SVar (0::nat),SVar 1]) (SFun () [SVar 1,SVar 0])"
  unfolding standard_step_def
  apply (intro conjI)
    apply (simp add: eq_binary_def)
   apply (simp add: eq_binary_def)
  apply (rule exI[of _ "SFun () [SVar (0::nat),SVar 1]"])
  apply (rule exI[of _ "SFun () [SVar (1::nat),SVar 0]"])
  apply (rule exI[of _ SHole])
  apply (rule exI[of _ SVar])
  by (simp add: equational_axioms_def correct_substitution_def)
lemma equational_equations_alone_terminate:
  "trs_equational_terminates eq_binary {} {} {()}"
  by (rule equational_empty_terminates)
lemma equational_below_root_nonground:
  "equational_step unary {(SFun () [SVar (0::nat)], SVar 0)} {} {}
    (SFun () [SFun () [SVar (7::nat)]]) (SFun () [SVar 7])"
  using below_root_nonground
  by (auto simp: equational_step_def equational_conversion_def intro: finite_steps.zero)

lemma equational_commuting_loop:
  "\<not> trs_equational_terminates eq_binary
    {(SFun () [SVar (0::nat), SVar 1], SFun () [SVar 1,SVar 0])} {} {()}"
proof -
  let ?s = "SFun () [SVar (0::nat),SVar 1]"
  let ?t = "SFun () [SVar (1::nat),SVar 0]"
  let ?R = "{(?s,?t)}"
  have strict: "standard_step eq_binary ?R ?s ?t"
    unfolding standard_step_def
    apply (intro conjI)
      apply (simp add: eq_binary_def)
     apply (simp add: eq_binary_def)
    apply (rule exI[of _ ?s], rule exI[of _ ?t])
    apply (rule exI[of _ SHole], rule exI[of _ SVar])
    by (simp add: correct_substitution_def)
  have reverse: "standard_step eq_binary (equational_axioms {} {()}) ?t ?s"
    unfolding standard_step_def
    apply (intro conjI)
      apply (simp add: eq_binary_def)
     apply (simp add: eq_binary_def)
    apply (rule exI[of _ ?t], rule exI[of _ ?s])
    apply (rule exI[of _ SHole], rule exI[of _ SVar])
    by (simp add: equational_axioms_def correct_substitution_def)
  have "equational_step eq_binary ?R {} {()} ?s ?s"
    unfolding equational_step_def equational_conversion_def
    using strict reverse by (meson finite_steps.zero finite_steps.append)
  then show ?thesis unfolding trs_equational_nontermination_iff
    by (intro exI[of _ "\<lambda>_. ?s"]) simp
qed
end
