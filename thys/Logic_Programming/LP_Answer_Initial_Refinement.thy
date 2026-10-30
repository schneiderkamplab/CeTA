theory LP_Answer_Initial_Refinement
 imports LP_Answer_Contracts
begin

text \<open>A checked normalization may replace the initial state while
preserving every immediate event and successor. The successor contracts and
all later answers remain obligations of the same transition system.\<close>
lemma lp_answer_contract_initial_refinement:
  fixes T :: "'s \<Rightarrow> 'a option \<Rightarrow> 's \<Rightarrow> bool"
    and normalized original :: "'s"
    and R :: "('b * 'b) set" and t :: "'b" and ret :: "'a \<Rightarrow> 'b"
  assumes contract: "lp_answer_contract T normalized R t ret"
    and reflects: "\<And>event tt. T original event tt \<Longrightarrow> T normalized event tt"
  shows "lp_answer_contract T original R t ret"
proof (rule lp_answer_contract_intro)
  fix event tt assume step: "T original event tt"
  have mapped: "T normalized event tt" by (rule reflects[OF step])
  have child: "lp_answer_contract T tt R t ret"
    by (rule lp_answer_contract_child[OF contract mapped])
  have event: "\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*"
    using contract mapped lp_answers_covered_event
    by (auto simp: lp_answer_contract_def)
  show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
    lp_answer_contract T tt R t ret" using event child by blast
qed

end
