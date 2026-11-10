theory LP_Cut_Domain_Return_Sequence
  imports LP_Cut_Domain_Return_Contracts
begin

context cut_runtime_domain
begin

lemma precise_resolve_prefix_projection:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
  assumes mgu: "mgu_resolve a (gs@rest) h bs \<sigma> \<rho>"
  shows "mgu_resolve a gs h bs \<sigma> \<rho>"
  unfolding mgu_resolve_def
proof (intro conjI allI impI)
  show "lp_isubst a \<sigma> = lp_ieval h \<rho>"
    using mgu by (simp add: mgu_resolve_def)
next
  fix x show "D (\<sigma> x)" using mgu by (auto simp: mgu_resolve_def)
next
  fix x show "D (\<rho> x)" using mgu by (auto simp: mgu_resolve_def)
next
  fix \<tau> \<nu> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assume dt: "\<forall>x. D (\<tau> x)" and dn: "\<forall>x. D (\<nu> x)"
    and eq: "lp_isubst a \<tau> = lp_ieval h \<nu>"
  obtain \<delta> where dd: "\<forall>x. D (\<delta> x)" and a: "lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau>"
    and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) (gs@rest) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) (gs@rest)"
    and body: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    using spec[OF spec[OF conjunct2[OF conjunct2[OF conjunct2[OF mgu[unfolded mgu_resolve_def]]]], of \<tau>], of \<nu>] dt dn eq by blast
  have prefix: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs"
    using arg_cong[OF goals, of "take (length gs)"] by simp
  show "\<exists>\<delta>. (\<forall>x. D (\<delta> x)) \<and> lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    using dd a prefix body by blast
qed

lemma precise_unify_prefix_projection:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
  assumes mgu: "mgu_unify a b (gs@rest) \<sigma>"
  shows "mgu_unify a b gs \<sigma>"
  unfolding mgu_unify_def
proof (intro conjI allI impI)
  show "lp_isubst a \<sigma> = lp_isubst b \<sigma>"
    using mgu by (simp add: mgu_unify_def)
next
  fix x show "D (\<sigma> x)" using mgu by (auto simp: mgu_unify_def)
next
  fix \<tau> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assume dt: "\<forall>x. D (\<tau> x)" and eq: "lp_isubst a \<tau> = lp_isubst b \<tau>"
  obtain \<delta> where dd: "\<forall>x. D (\<delta> x)" and a: "lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau>"
    and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) (gs@rest) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) (gs@rest)"
    using spec[OF conjunct2[OF conjunct2[OF mgu[unfolded mgu_unify_def]]], of \<tau>] dt eq by blast
  have prefix: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs"
    using arg_cong[OF goals, of "take (length gs)"] by simp
  show "\<exists>\<delta>. (\<forall>x. D (\<delta> x)) \<and> lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs"
    using dd a prefix by blast
qed

inductive_set precise_return_sequence for P C start finished where
  prefix: "precise_answer_transition P ss None tt \<Longrightarrow>
    (LPCPrefix ss,LPCPrefix tt)\<in>precise_return_sequence P C start finished"
| returned: "precise_answer_transition P ss (Some \<eta>) tt \<Longrightarrow>
    (LPCPrefix ss,LPCContinue (start \<eta>) tt)\<in>precise_return_sequence P C start finished"
| child: "(c,d)\<in>C \<Longrightarrow>
    (LPCContinue c ss,LPCContinue d ss)\<in>precise_return_sequence P C start finished"
| resume: "finished c \<Longrightarrow>
    (LPCContinue c ss,LPCPrefix ss)\<in>precise_return_sequence P C start finished"

lemma precise_return_sequence_continue_SN:
  assumes child: "SN_on C {c}"
    and resumed: "SN_on (precise_return_sequence P C start finished) {LPCPrefix ss}"
  shows "SN_on (precise_return_sequence P C start finished) {LPCContinue c ss}"
proof (rule SN_on_induct[OF child singletonI])
  fix c
  assume ih: "\<And>d. (c,d)\<in>C \<Longrightarrow>
    SN_on (precise_return_sequence P C start finished) {LPCContinue d ss}"
  show "SN_on (precise_return_sequence P C start finished) {LPCContinue c ss}"
  proof (rule step_reflects_SN_on)
    fix x assume step: "(LPCContinue c ss,x)\<in>precise_return_sequence P C start finished"
    then show "SN_on (precise_return_sequence P C start finished) {x}"
      using ih resumed by (cases rule: precise_return_sequence.cases) auto
  qed
qed

theorem precise_return_sequence_SN:
  assumes prefix_sn: "SN_on (precise_answer_steps P) {ss}"
    and answers: "\<And>us \<eta> tt. (ss,us)\<in>(precise_answer_steps P)\<^sup>* \<Longrightarrow>
      precise_answer_transition P us (Some \<eta>) tt \<Longrightarrow> SN_on C {start \<eta>}"
  shows "SN_on (precise_return_sequence P C start finished) {LPCPrefix ss}"
proof -
  have all: "(ss,us)\<in>(precise_answer_steps P)\<^sup>* \<longrightarrow>
    SN_on (precise_return_sequence P C start finished) {LPCPrefix us}"
    if sn: "SN_on (precise_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro impI)
    fix us
    assume ih: "\<And>tt. (us,tt)\<in>precise_answer_steps P \<Longrightarrow>
      (ss,tt)\<in>(precise_answer_steps P)\<^sup>* \<longrightarrow>
      SN_on (precise_return_sequence P C start finished) {LPCPrefix tt}"
      and path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    have next_sn: "SN_on (precise_return_sequence P C start finished) {LPCPrefix tt}"
      if event: "precise_answer_transition P us e tt" for e tt
    proof -
      have step: "(us,tt)\<in>precise_answer_steps P"
        using event by (auto simp: precise_answer_steps_def)
      have reached: "(ss,tt)\<in>(precise_answer_steps P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF path step])
      show ?thesis using ih[OF step] reached by blast
    qed
    show "SN_on (precise_return_sequence P C start finished) {LPCPrefix us}"
    proof (rule step_reflects_SN_on)
      fix x assume step: "(LPCPrefix us,x)\<in>precise_return_sequence P C start finished"
      from step show "SN_on (precise_return_sequence P C start finished) {x}"
      proof cases
        case (prefix tt)
        have event: "precise_answer_transition P us None tt" using prefix by simp
        show ?thesis using next_sn[OF event] prefix by simp
      next
        case (returned \<eta> tt)
        have event: "precise_answer_transition P us (Some \<eta>) tt" using returned by simp
        have child: "SN_on C {start \<eta>}" by (rule answers[OF path event])
        have resume_sn: "SN_on (precise_return_sequence P C start finished) {LPCPrefix tt}"
          by (rule next_sn[OF event])
        show ?thesis using precise_return_sequence_continue_SN[OF child resume_sn] returned by simp
      qed
    qed
  qed
  show ?thesis using all[OF prefix_sn] by simp
qed

corollary precise_return_contract_sequence_SN:
  assumes contract: "precise_return_contract P ss R t ret"
    and continuation: "\<And>\<eta>. (t,ret \<eta>)\<in>R\<^sup>* \<Longrightarrow> SN_on C {start \<eta>}"
  shows "SN_on (precise_return_sequence P C start finished) {LPCPrefix ss}"
proof (rule precise_return_sequence_SN)
  show "SN_on (precise_answer_steps P) {ss}"
    using contract precise_answer_instrumentation_SN
    unfolding precise_return_contract_def by blast
next
  fix us \<eta> tt
  assume path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some \<eta>) tt"
  show "SN_on C {start \<eta>}"
    by (rule precise_return_contract_success[OF contract path event continuation])
qed


end
end
