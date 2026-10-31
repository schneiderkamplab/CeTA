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


text \<open>A library expansion needs coverage of every primitive successor,
not merely an upper bound on the library's successful answers. Its complete
termination-and-answer contract remains a premise. Reachability is in the same
instrumented transition system, retaining environments and saved alternatives.\<close>
lemma lp_answer_contract_reachable:
  assumes contract: "lp_answer_contract T ss R t ret"
    and path: "(ss,tt)\<in>(lp_answer_steps T)\<^sup>*"
  shows "lp_answer_contract T tt R t ret"
  using path contract
proof (induction rule: rtrancl_induct)
  case base then show ?case .
next
  case (step us vs)
  obtain event where edge: "T us event vs"
    using step.hyps(2) by (auto simp: lp_answer_steps_def)
  show ?case by (rule lp_answer_contract_child[OF step.IH[OF step.prems] edge])
qed

lemma lp_answer_contract_silent_expansion:
  assumes contract: "lp_answer_contract T expanded R t ret"
    and coverage: "\<And>event tt. T original event tt \<Longrightarrow>
      event=None \<and> (expanded,tt)\<in>(lp_answer_steps T)\<^sup>*"
  shows "lp_answer_contract T original R t ret"
proof (rule lp_answer_contract_intro)
  fix event tt assume step: "T original event tt"
  have silent: "event=None" and path:
    "(expanded,tt)\<in>(lp_answer_steps T)\<^sup>*"
    using coverage[OF step] by auto
  have child: "lp_answer_contract T tt R t ret"
    by (rule lp_answer_contract_reachable[OF contract path])
  show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
    lp_answer_contract T tt R t ret" using silent child by simp
qed

ML \<open>
val checked = [@{thm lp_answer_contract_reachable},
  @{thm lp_answer_contract_silent_expansion}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted library expansion contract dependency" else ();
\<close>
end
