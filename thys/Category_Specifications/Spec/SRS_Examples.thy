theory SRS_Examples
  imports SRS_Standard_Spec SRS_Relative_Spec SRS_Cycle_Spec
begin
lemma empty_strings: "srs_standard_terminates {}"
  by (simp add: srs_standard_terminates_def no_infinite_steps_def string_step_def)
lemma empty_strict_strings: "srs_relative_terminates {} S"
  by (simp add: srs_relative_terminates_def no_infinite_steps_def relative_string_step_def string_step_def)
lemma empty_cycles: "srs_cycle_terminates {}"
  by (simp add: srs_cycle_terminates_def no_infinite_steps_def cycle_string_step_def string_step_def)

lemma word_self_loop:
  "\<not> srs_standard_terminates {(w,w)}"
proof -
  have "string_step {(w,w)} w w"
    unfolding string_step_def
    by (intro exI[of _ w] exI[of _ w] exI[of _ "[]"] exI[of _ "[]"]) simp
  then show ?thesis unfolding srs_standard_nontermination_iff
    by (intro exI[of _ "\<lambda>_. w"]) simp
qed
lemma empty_word_is_allowed: "string_problem {([],[]::nat list)}"
  by (simp add: string_problem_def)
lemma weak_word_loop_allowed: "srs_relative_terminates {} {(w,w)}"
  by (rule empty_strict_strings)
lemma replacement_inside_word:
  "string_step {([a],[])} [b,a,c] [b,c]"
  unfolding string_step_def
  by (intro exI[of _ "[a]"] exI[of _ "[]"] exI[of _ "[b]"] exI[of _ "[c]"]) simp
lemma deleting_symbol_decreases:
  "string_step {([a],[])} s t \<Longrightarrow> length t < length s"
  by (auto simp: string_step_def)
lemma deleting_symbol_terminates: "srs_standard_terminates {([a],[])}"
proof (unfold srs_standard_terminates_def no_infinite_steps_def, clarify)
  fix ws
  assume steps: "\<forall>i. string_step {([a],[])} (ws i) (ws (Suc i))"
  have bound: "\<And>n. length (ws n) + n \<le> length (ws 0)"
  proof -
    fix n
    show "length (ws n) + n \<le> length (ws 0)"
    proof (induct n)
      case 0 then show ?case by simp
    next
      case (Suc n)
      have "length (ws (Suc n)) < length (ws n)"
        by (rule deleting_symbol_decreases[OF steps[rule_format]])
      then show ?case using Suc by arith
    qed
  qed
  from bound[of "Suc (length (ws 0))"] show False by simp
qed

text \<open>The replacement ab to ba is a cycle self-loop: rotate its result.
This is a real replacement, not a rotation counted as progress.\<close>
lemma rotation_after_replacement:
  "cycle_string_step {([a,b],[b,a])} [a,b] [a,b]"
proof -
  have step: "string_step {([a,b],[b,a])} [a,b] [b,a]"
    unfolding string_step_def
    by (intro exI[of _ "[a,b]"] exI[of _ "[b,a]"] exI[of _ "[]"] exI[of _ "[]"]) simp
  show ?thesis unfolding cycle_string_step_def
    by (intro exI[of _ "[]"] exI[of _ "[a,b]"] exI[of _ "[b]"] exI[of _ "[a]"]) (simp add: step)
qed
lemma rotation_cycle_nonterminates:
  "\<not> srs_cycle_terminates {([a,b],[b,a])}"
  unfolding srs_cycle_nontermination_iff
  by (intro exI[of _ "\<lambda>_. [a,b]"]) (simp add: rotation_after_replacement)
end
