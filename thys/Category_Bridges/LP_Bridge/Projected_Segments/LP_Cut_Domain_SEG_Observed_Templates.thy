theory LP_Cut_Domain_SEG_Observed_Templates
 imports LP_Cut_Domain_SEG_Observed_Control
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_seg_observer_emit:
  fixes m :: "('g,string) term" and initial
  assumes checked: "lpc_seg_check_observer_emits filtering is_cont c d R inp outp states"
    and index: "i<length states"
    and inv: "lpc_seg_observer_invariant filtering is_cont c d inp m (lpc_return_eval eta (states!i))"
    and event: "precise_answer_transition P (lpc_return_eval eta (states!i)) (Some rho) tt"
    and initial: "lp_iproject filtering initial m"
  shows "(initial,lpc_seg_runtime_value is_cont c d outp rho)\<in>lpc_seg_projected_rel filtering R"
proof -
  have runtime: "lpc_return_eval eta (states!i)=(LPCGoals [],rho)#tt"
    using event by (cases rule: precise_answer_transition.cases) auto
  obtain e obs rest where state: "states!i=(e,obs)#rest"
    using runtime by (cases "states!i") (auto simp: lpc_return_eval_def)
  have head: "lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e=LPCGoals []"
    and rho: "rho=lpc_return_env obs eta"
    using runtime by (simp_all add: state lpc_return_eval_def)
  have e: "e=LPCGoals []" using head by (cases e) auto
  have shape: "states!i=(LPCGoals [],obs)#rest" by (simp only: state e)
  have pair: "lpc_seg_check_projected_pair filtering 1 1 is_cont c d R
    (lpc_seg_compose_observation obs inp) (lpc_seg_compose_observation obs outp)"
    using checked[unfolded lpc_seg_check_observer_emits_def list_all_iff,
      rule_format, OF nth_mem[OF index]]
    by (simp only: shape) simp
  have left: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d
    (lp_ieval (lpc_seg_compose_observation obs inp) eta)) m"
    using lpc_seg_observer_boundary[OF inv shape] by (simp only: lpc_seg_runtime_value_def)
  obtain n where pr: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d
      (lp_ieval (lpc_seg_compose_observation obs outp) eta)) n"
    and step: "(m,n)\<in>rstep (af_rule filtering ` R)"
    by (rule lpc_seg_checked_projected_pair[OF pair left]) blast
  show ?thesis using initial pr step
    by (auto simp: lpc_seg_projected_rel_def lpc_seg_runtime_value_def rho lpc_seg_observer_eval)
qed


end
end
