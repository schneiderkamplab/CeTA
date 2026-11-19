theory LP_Cut_Domain_Return_Coverage
  imports LP_Cut_Domain_Return_Triples
begin

context cut_runtime_domain
begin

definition precise_answers_covered where
  "precise_answers_covered P ss C = (\<forall>us rho vs.
    (ss,us)\<in>(precise_answer_steps P)\<^sup>* \<longrightarrow>
    precise_answer_transition P us (Some rho) vs \<longrightarrow> C rho)"

lemma precise_answers_covered_event:
  "precise_answers_covered P ss C \<Longrightarrow>
    precise_answer_transition P ss (Some rho) tt \<Longrightarrow> C rho"
  by (auto simp: precise_answers_covered_def)

lemma precise_answers_covered_child:
  assumes covered: "precise_answers_covered P ss C"
    and step: "precise_answer_transition P ss event tt"
  shows "precise_answers_covered P tt C"
proof (unfold precise_answers_covered_def, intro allI impI)
  fix us rho vs
  assume path: "(tt,us)\<in>(precise_answer_steps P)\<^sup>*"
    and success: "precise_answer_transition P us (Some rho) vs"
  have edge: "(ss,tt)\<in>precise_answer_steps P"
    using step by (auto simp: precise_answer_steps_def)
  have "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    by (rule converse_rtrancl_into_rtrancl[OF edge path])
  then show "C rho" using covered success by (auto simp: precise_answers_covered_def)
qed

lemma precise_answers_covered_intro:
  assumes local: "\<And>event tt. precise_answer_transition P ss event tt \<Longrightarrow>
    (\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> precise_answers_covered P tt C"
  shows "precise_answers_covered P ss C"
proof (unfold precise_answers_covered_def, intro allI impI)
  fix us rho vs
  assume path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and success: "precise_answer_transition P us (Some rho) vs"
  from path show "C rho"
  proof (cases rule: converse_rtranclE)
    case base then show ?thesis using local success by blast
  next
    case (step tt)
    obtain event where event: "precise_answer_transition P ss event tt"
      using step by (auto simp: precise_answer_steps_def)
    show ?thesis using local[OF event] step success
      by (auto simp: precise_answers_covered_def)
  qed
qed


end
end
