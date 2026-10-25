theory LP_Cut_SEG_Observations
  imports LP_Cut_SEG_Reinterface LP_Cut_SEG_Measure
begin

lemma lpc_seg_position_eval:
  assumes distinct: "distinct vs" and variables: "vars_term t \<subseteq> set vs"
  shows "lp_ieval (lpc_seg_position_template vs t) (lpc_return_env (map Var vs) eta) = lp_ieval t eta"
  using variables
proof (induct t)
  case (Var x)
  obtain i where index: "i<length vs" and x: "x=vs!i" using Var.prems by (auto simp: in_set_conv_nth)
  have lookup: "map_of (zip vs [0..<length vs]) x = Some i"
    using map_of_zip_nth[of vs "[0..<length vs]" i] distinct index x by simp
  show ?case by (simp add: lpc_seg_position_template_def lookup[unfolded x] lpc_return_env_def index x)
next
  case (Fun f ts)
  have children: "\<And>u. u\<in>set ts \<Longrightarrow>
      lp_ieval (lpc_seg_position_template vs u) (lpc_return_env (map Var vs) eta) = lp_ieval u eta"
    using Fun.hyps Fun.prems by auto
  show ?case using children by (simp add: lpc_seg_position_template_def map_map o_def cong: map_cong)
qed

lemma lpc_seg_observe_environment:
  assumes distinct: "distinct vs"
    and variables: "\<And>t. t\<in>set ts \<Longrightarrow> vars_term t \<subseteq> set vs"
  shows "lpc_seg_observe (map (lpc_seg_position_template vs) ts) (lpc_return_env (map Var vs) eta) =
    lpc_return_env ts eta"
proof (rule ext)
  fix i
  show "lpc_seg_observe (map (lpc_seg_position_template vs) ts) (lpc_return_env (map Var vs) eta) i =
      lpc_return_env ts eta i"
  proof (cases "i<length ts")
    case True
    have vars: "vars_term (ts!i) \<subseteq> set vs" by (rule variables[OF nth_mem[OF True]])
    have equal: "lp_ieval (lpc_seg_position_template vs (ts!i)) (lpc_return_env (map Var vs) eta) = lp_ieval (ts!i) eta"
      by (rule lpc_seg_position_eval[OF distinct vars])
    show ?thesis using equal True by (simp add: lpc_seg_observe_def lpc_return_env_def)
  next
    case False then show ?thesis by (simp add: lpc_seg_observe_def lpc_return_env_def)
  qed
qed

lemma lpc_seg_observe_singleton:
  assumes distinct: "distinct vs"
    and variables: "\<And>t. t\<in>set ts \<Longrightarrow> vars_term t \<subseteq> set vs"
  shows "lpc_reinterface (lpc_seg_observe (map (lpc_seg_position_template vs) ts))
      (lpc_return_eval eta [(e,map Var vs)]) = lpc_return_eval eta [(e,ts)]"
  by (simp add: lpc_reinterface_def lpc_return_eval_def lpc_seg_observe_environment[OF distinct variables])

definition lpc_seg_compose_observation where
  "lpc_seg_compose_observation templates t = t\<cdot>
    (\<lambda>i. if i<length templates then templates!i else Fun LPCTruth [])"

lemma lpc_seg_observation_eval:
  "lp_ieval t (lpc_seg_observe templates rho) =
    lp_ieval (lpc_seg_compose_observation templates t) rho"
  unfolding lpc_seg_compose_observation_def lp_ieval_finite_subst
  by (rule lp_ieval_cong) (simp add: lpc_seg_observe_def)

end
