theory LP_Cut_Return_Sequence
  imports LP_Cut_Return_Contracts
begin

text \<open>Removing the suspended continuation preserves the most-general
property on the remaining prefix interface. These are one-way projections:
the reverse direction would incorrectly assume independence of live variables
shared with the suspended continuation.\<close>

lemma lpc_mgu_resolve_prefix_projection:
  fixes a :: "('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve a (gs@rest) h bs \<sigma> \<rho>"
  shows "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
  unfolding lpc_mgu_resolve_def
proof (intro conjI allI impI)
  show "lp_isubst a \<sigma> = lp_ieval h \<rho>"
    using mgu by (simp add: lpc_mgu_resolve_def)
next
  fix \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume eq: "lp_isubst a \<tau> = lp_ieval h \<nu>"
  obtain \<delta> where a: "lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau>"
    and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) (gs@rest) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) (gs@rest)"
    and body: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    using mgu eq unfolding lpc_mgu_resolve_def by blast
  have prefix: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs"
    using arg_cong[OF goals, of "take (length gs)"] by simp
  show "\<exists>\<delta>. lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    using a prefix body by blast
qed

lemma lpc_mgu_unify_prefix_projection:
  fixes a :: "('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_unify a b (gs@rest) \<sigma>"
  shows "lpc_mgu_unify a b gs \<sigma>"
  unfolding lpc_mgu_unify_def
proof (intro conjI allI impI)
  show "lp_isubst a \<sigma> = lp_isubst b \<sigma>"
    using mgu by (simp add: lpc_mgu_unify_def)
next
  fix \<tau> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume eq: "lp_isubst a \<tau> = lp_isubst b \<tau>"
  obtain \<delta> where a: "lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau>"
    and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) (gs@rest) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) (gs@rest)"
    using mgu eq unfolding lpc_mgu_unify_def by blast
  have prefix: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs"
    using arg_cong[OF goals, of "take (length gs)"] by simp
  show "\<exists>\<delta>. lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs"
    using a prefix by blast
qed

text \<open>The sequencing machine executes a continuation for each successful
prefix return, then resumes the remaining prefix alternatives. In particular it
does not equate a single success with exhaustion of the prefix search. This
machine is a semantic composition layer; attachment to concrete source goals
requires a separate simulation, including cut scopes and live environments.\<close>

datatype ('s,'c) lpc_return_phase = LPCPrefix 's | LPCContinue 'c 's

inductive_set lpc_return_sequence for P C start finished where
  prefix: "lpc_answer_transition P ss None tt \<Longrightarrow>
    (LPCPrefix ss,LPCPrefix tt)\<in>lpc_return_sequence P C start finished"
| returned: "lpc_answer_transition P ss (Some \<eta>) tt \<Longrightarrow>
    (LPCPrefix ss,LPCContinue (start \<eta>) tt)\<in>lpc_return_sequence P C start finished"
| child: "(c,d)\<in>C \<Longrightarrow>
    (LPCContinue c ss,LPCContinue d ss)\<in>lpc_return_sequence P C start finished"
| resume: "finished c \<Longrightarrow>
    (LPCContinue c ss,LPCPrefix ss)\<in>lpc_return_sequence P C start finished"

lemma lpc_return_sequence_continue_SN:
  assumes child: "SN_on C {c}"
    and resumed: "SN_on (lpc_return_sequence P C start finished) {LPCPrefix ss}"
  shows "SN_on (lpc_return_sequence P C start finished) {LPCContinue c ss}"
proof (rule SN_on_induct[OF child singletonI])
  fix c
  assume ih: "\<And>d. (c,d)\<in>C \<Longrightarrow>
    SN_on (lpc_return_sequence P C start finished) {LPCContinue d ss}"
  show "SN_on (lpc_return_sequence P C start finished) {LPCContinue c ss}"
  proof (rule step_reflects_SN_on)
    fix x assume step: "(LPCContinue c ss,x)\<in>lpc_return_sequence P C start finished"
    then show "SN_on (lpc_return_sequence P C start finished) {x}"
      using ih resumed by (cases rule: lpc_return_sequence.cases) auto
  qed
qed

theorem lpc_return_sequence_SN:
  assumes prefix_sn: "SN_on (lpc_answer_steps P) {ss}"
    and answers: "\<And>us \<eta> tt. (ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<Longrightarrow>
      lpc_answer_transition P us (Some \<eta>) tt \<Longrightarrow> SN_on C {start \<eta>}"
  shows "SN_on (lpc_return_sequence P C start finished) {LPCPrefix ss}"
proof -
  have all: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<longrightarrow>
    SN_on (lpc_return_sequence P C start finished) {LPCPrefix us}"
    if sn: "SN_on (lpc_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro impI)
    fix us
    assume ih: "\<And>tt. (us,tt)\<in>lpc_answer_steps P \<Longrightarrow>
      (ss,tt)\<in>(lpc_answer_steps P)\<^sup>* \<longrightarrow>
      SN_on (lpc_return_sequence P C start finished) {LPCPrefix tt}"
      and path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    have next_sn: "SN_on (lpc_return_sequence P C start finished) {LPCPrefix tt}"
      if event: "lpc_answer_transition P us e tt" for e tt
    proof -
      have step: "(us,tt)\<in>lpc_answer_steps P"
        using event by (auto simp: lpc_answer_steps_def)
      have reached: "(ss,tt)\<in>(lpc_answer_steps P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF path step])
      show ?thesis using ih[OF step] reached by blast
    qed
    show "SN_on (lpc_return_sequence P C start finished) {LPCPrefix us}"
    proof (rule step_reflects_SN_on)
      fix x assume step: "(LPCPrefix us,x)\<in>lpc_return_sequence P C start finished"
      from step show "SN_on (lpc_return_sequence P C start finished) {x}"
      proof cases
        case (prefix tt)
        have event: "lpc_answer_transition P us None tt" using prefix by simp
        show ?thesis using next_sn[OF event] prefix by simp
      next
        case (returned \<eta> tt)
        have event: "lpc_answer_transition P us (Some \<eta>) tt" using returned by simp
        have child: "SN_on C {start \<eta>}" by (rule answers[OF path event])
        have resume_sn: "SN_on (lpc_return_sequence P C start finished) {LPCPrefix tt}"
          by (rule next_sn[OF event])
        show ?thesis using lpc_return_sequence_continue_SN[OF child resume_sn] returned by simp
      qed
    qed
  qed
  show ?thesis using all[OF prefix_sn] by simp
qed

corollary lpc_return_contract_sequence_SN:
  assumes contract: "lpc_return_contract P ss R t ret"
    and continuation: "\<And>\<eta>. (t,ret \<eta>)\<in>R\<^sup>* \<Longrightarrow> SN_on C {start \<eta>}"
  shows "SN_on (lpc_return_sequence P C start finished) {LPCPrefix ss}"
proof (rule lpc_return_sequence_SN)
  show "SN_on (lpc_answer_steps P) {ss}"
    using contract lpc_answer_instrumentation_SN
    unfolding lpc_return_contract_def by blast
next
  fix us \<eta> tt
  assume path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some \<eta>) tt"
  show "SN_on C {start \<eta>}"
    by (rule lpc_return_contract_success[OF contract path event continuation])
qed

end
