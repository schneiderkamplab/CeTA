theory LP_Answer_Block_Invariant
 imports LP_Answer_Contracts
begin

text \<open>Return safety for one- or two-step blocks needs no termination
premise. Every answer and later alternative is covered. The internal phase
must be silent on every outgoing transition and return to the invariant.\<close>

definition lp_answer_block_invariant where
 "lp_answer_block_invariant T I ss =
  (I ss \<or> (\<forall>event tt. T ss event tt \<longrightarrow> event=None \<and> I tt))"

lemma lp_answers_covered_two_step_blocks:
 assumes initial: "I ss"
 and local: "\<And>us event vs. I us \<Longrightarrow> T us event vs \<Longrightarrow>
   (\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> lp_answer_block_invariant T I vs"
 shows "lp_answers_covered T ss C"
proof -
 have preserved: "lp_answer_block_invariant T I vs"
  if invariant: "lp_answer_block_invariant T I us" and edge: "(us,vs)\<in>lp_answer_steps T" for us vs
 proof -
  obtain event where step: "T us event vs" using edge by (auto simp: lp_answer_steps_def)
  show ?thesis using invariant local[OF _ step] step
   by (auto simp: lp_answer_block_invariant_def)
 qed
 have reachable: "lp_answer_block_invariant T I us"
  if path: "(ss,us)\<in>(lp_answer_steps T)\<^sup>*" for us
  using path
  by (induction rule: rtrancl_induct) (use initial preserved in \<open>auto simp: lp_answer_block_invariant_def\<close>)
 show ?thesis
 proof (unfold lp_answers_covered_def, intro allI impI)
  fix us rho vs
  assume path: "(ss,us)\<in>(lp_answer_steps T)\<^sup>*" and answer: "T us (Some rho) vs"
  show "C rho" using reachable[OF path] answer local[OF _ answer]
   by (auto simp: lp_answer_block_invariant_def)
 qed
qed

lemma lp_two_step_block_preserves_answers:
 assumes initial: "I ss"
 and returned: "\<And>us rho vs. I us \<Longrightarrow> T us (Some rho) vs \<Longrightarrow> C rho"
 and steps: "\<And>us event vs. I us \<Longrightarrow> T us event vs \<Longrightarrow>
   I vs \<or> (\<forall>next ws. T vs next ws \<longrightarrow> next=None \<and> I ws)"
 shows "lp_answers_covered T ss C"
 by (rule lp_answers_covered_two_step_blocks[where I=I, OF initial])
  (use returned steps in \<open>auto simp: lp_answer_block_invariant_def\<close>)

end
