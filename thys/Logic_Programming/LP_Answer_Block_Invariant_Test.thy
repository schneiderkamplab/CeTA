theory LP_Answer_Block_Invariant_Test
 imports LP_Answer_Block_Invariant
begin

lemma lp_silent_divergence_has_answer_safety:
 "lp_answers_covered (\<lambda>(s::nat) event t. event=(None::bool option) \<and> t=s) 0 (\<lambda>_. False)"
 by (rule lp_two_step_block_preserves_answers[where I="\<lambda>_. True"])
  auto

lemma lp_later_bad_answer_not_covered:
 "\<not>lp_answers_covered
   (\<lambda>(s::nat) event t. (s=0 \<and> event=Some True \<and> t=1) \<or>
    (s=1 \<and> event=Some False \<and> t=1)) 0 id"
proof -
 let ?T = "\<lambda>(s::nat) event t. (s=0 \<and> event=Some True \<and> t=1) \<or>
    (s=1 \<and> event=Some False \<and> t=1)"
 have first: "?T 0 (Some True) 1" by simp
 have later: "?T 1 (Some False) 1" by simp
 show ?thesis
  using lp_answers_covered_child[where T="?T" and C=id, OF _ first]
   lp_answers_covered_event[where T="?T" and C=id, OF _ later] by auto
qed

lemma lp_answering_internal_phase_rejected:
 "\<not>lp_answer_block_invariant
   (\<lambda>(s::nat) event t. s=1 \<and> event=Some False \<and> t=0)
   (\<lambda>s. s=0) 1"
 by (auto simp: lp_answer_block_invariant_def)

end
