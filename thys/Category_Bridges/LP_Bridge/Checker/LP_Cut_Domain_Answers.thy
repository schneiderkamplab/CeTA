theory LP_Cut_Domain_Answers
  imports LP_Cut_Domain_Control
begin

context cut_runtime_domain
begin

text \<open>Answer tracking retains the native residual derivation and records
that its change to the caller's valuation is a substitution in the chosen
domain. Native groundness and reachability results can then be reused.\<close>
inductive_set answer_step ::
  "('f lp_cut_symbol,string) lp_clause list \<Rightarrow>
    ((('f lp_cut_symbol,string) lp_iatom list \<times>
      (string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm))) rel"
  for P where
  step: "((gs,eta),(hs,\<lambda>x. lp_isubst (eta x) sigma)) \<in> lp_seg_answer_step P \<Longrightarrow>
    (\<forall>x. D (sigma x)) \<Longrightarrow>
    ((gs,eta),(hs,\<lambda>x. lp_isubst (eta x) sigma)) \<in> answer_step P"

lemma answer_step_native:
  assumes step: "((gs,eta),(hs,rho))\<in>answer_step P"
  shows "((gs,eta),(hs,rho))\<in>lp_seg_answer_step P"
  using step by (induct rule: answer_step.induct) assumption
lemma answer_paths_native:
  "(s,t)\<in>(answer_step P)\<^sup>* \<Longrightarrow> (s,t)\<in>(lp_seg_answer_step P)\<^sup>*"
  by (rule rtrancl_mono[THEN subsetD]) (auto dest: answer_step_native)
lemma answer_step_erases:
  "((gs,eta),(hs,rho))\<in>answer_step P \<Longrightarrow> (gs,hs)\<in>lp_ild P"
  by (rule lp_seg_answer_step_erases[OF answer_step_native])

lemma answer_negative_guard:
  assumes negative: "lpc_answer_negative_guard g" and known: "guard_holds g eta"
    and ds: "\<And>x. D (sigma x)"
  shows "guard_holds g (\<lambda>x. lp_isubst (eta x) sigma)"
proof (cases g)
  case (LPCHeadGuard a h b)
  have b: "b=False" using negative by (simp add: LPCHeadGuard)
  have no: "\<not>(\<exists>tau rho. (\<forall>x. D (tau x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst (lp_ieval a eta) tau = lp_ieval h rho)"
    using known by (simp add: LPCHeadGuard b cut_domain_head_def)
  show ?thesis using head_negative[OF no ds]
    by (simp add: LPCHeadGuard b cut_domain_head_def lp_ieval_subst)
next
  case (LPCEqGuard a c b)
  have b: "b=False" using negative by (simp add: LPCEqGuard)
  have no: "\<not>(\<exists>tau. (\<forall>x. D (tau x)) \<and>
    lp_isubst (lp_ieval a eta) tau = lp_isubst (lp_ieval c eta) tau)"
    using known by (simp add: LPCEqGuard b cut_domain_equality_def)
  show ?thesis using equality_negative[OF no ds]
    by (simp add: LPCEqGuard b cut_domain_equality_def lp_ieval_subst)
qed

lemma answer_knowledge_step:
  assumes step: "((gs,eta),(hs,rho))\<in>answer_step P"
    and known: "knowledge G K eta" and negative: "list_all lpc_answer_negative_guard K"
  shows "knowledge G K rho"
proof -
  from step obtain sigma where ds: "\<And>x. D (sigma x)"
    and rho: "rho=(\<lambda>x. lp_isubst (eta x) sigma)" by (cases rule: answer_step.cases) auto
  have domain: "\<forall>x. D (rho x)"
    unfolding rho by (intro allI; rule substitute[OF knowledge_domain[OF known] ds])
  have guards: "\<forall>g\<in>set K. guard_holds g rho"
    using known negative answer_negative_guard[OF _ _ ds]
    by (auto simp: knowledge_def list_all_iff rho)
  show ?thesis using known domain guards
    by (auto simp: knowledge_def rho lp_seg_ground_subst list_all_iff)
qed

lemma answer_knowledge_path:
  assumes path: "((gs,eta),(hs,rho))\<in>(answer_step P)\<^sup>*"
    and known: "knowledge G K eta" and negative: "list_all lpc_answer_negative_guard K"
  shows "knowledge G K rho"
  using path known
  by (induct rule: rtrancl_induct2) (auto intro: answer_knowledge_step[OF _ _ negative])

lemma answer_outputs:
  assumes checked: "lp_ground_check Q modes"
    and path: "((map (\<lambda>a. lp_atom_eval a eta) goals,eta),([],rho))\<in>(answer_step Q)\<^sup>*"
    and known: "knowledge G K eta"
    and grounds: "G' \<subseteq> lp_ground_flow modes goals G"
    and guards: "set K' \<subseteq> set (filter lpc_answer_negative_guard K)"
  shows "knowledge G' K' rho"
proof -
  have ground: "\<forall>x\<in>G. lp_seg_ground (eta x)" using known by (simp add: knowledge_def)
  have outputs: "\<forall>x\<in>lp_ground_flow modes goals G. lp_seg_ground (rho x)"
    by (rule lp_ground_check_answers[OF checked answer_paths_native[OF path] ground])
  have incoming: "knowledge G K' eta" using known guards
    by (auto simp: knowledge_def list_all_iff)
  have negative: "list_all lpc_answer_negative_guard K'" using guards
    by (auto simp: list_all_iff)
  have keep: "knowledge G K' rho" by (rule answer_knowledge_path[OF path incoming negative])
  show ?thesis using outputs keep grounds by (auto simp: knowledge_def)
qed

end
end
