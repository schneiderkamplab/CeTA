theory LP_Cut_SEG_Interfaces
  imports LP_Cut_Return_Interface_Lift LP_Cut_SEG_TRS_Returns
begin

text \<open>Connection endpoints may rebuild the caller's observed answer from
the callee's variables. This is a finite term substitution, not a requirement
that accumulated answer labels match at INST. Saved alternatives are mapped
individually, and the observation commutes with every source unifier.\<close>

definition lpc_seg_observe where
  "lpc_seg_observe templates eta n = (if n<length templates
     then lp_ieval (templates!n) eta else LPIFun LPCTruth [])"

lemma lpc_seg_observe_commutes:
  "lpc_seg_observe templates (\<lambda>x. lp_isubst (eta x) sigma) =
    (\<lambda>n. lp_isubst (lpc_seg_observe templates eta n) sigma)"
  by (rule ext) (simp add: lpc_seg_observe_def lp_ieval_subst)

definition lpc_seg_reinterface where
  "lpc_seg_reinterface templates ss = map (\<lambda>(e,ts). (e,
    map (\<lambda>t. t\<cdot>(\<lambda>n. if n<length ts then ts!n else Fun LPCTruth [])) templates)) ss"

lemma lpc_seg_observe_finite:
  "lpc_seg_observe templates (lpc_return_env ts eta) =
    lpc_return_env (map (\<lambda>t. t\<cdot>(\<lambda>n. if n<length ts then ts!n else Fun LPCTruth [])) templates) eta"
proof -
  have env: "(\<lambda>n. lp_ieval (if n<length ts then ts!n else Fun LPCTruth []) eta) = lpc_return_env ts eta"
    by (rule ext) (simp add: lpc_return_env_def)
  show ?thesis
    by (rule ext) (simp add: lpc_seg_observe_def lpc_return_env_def lp_ieval_finite_subst env)
qed

lemma lpc_seg_reinterface_sound:
  "lpc_return_eval eta (lpc_seg_reinterface templates ss) =
    lpc_reinterface (lpc_seg_observe templates) (lpc_return_eval eta ss)"
  by (simp add: lpc_return_eval_def lpc_seg_reinterface_def lpc_reinterface_def
    map_map o_def split_def lpc_seg_observe_finite)

theorem lpc_seg_instance_return_contract:
  assumes child: "lpc_return_contract P (lpc_return_eval eta ss) R u ret"
    and entry: "(t,u)\<in>R\<^sup>*"
    and bridge: "\<And>rho. (ret rho,final (lpc_seg_observe templates rho))\<in>R\<^sup>*"
  shows "lpc_return_contract P (lpc_return_eval eta (lpc_seg_reinterface templates ss)) R t final"
proof -
  have projected: "lpc_return_contract P
    (lpc_reinterface (lpc_seg_observe templates) (lpc_return_eval eta ss)) R u final"
    by (rule lpc_return_contract_project[where F="lpc_seg_observe templates", OF lpc_seg_observe_commutes child bridge])
  have renamed: "lpc_return_contract P (lpc_return_eval eta (lpc_seg_reinterface templates ss)) R u final"
    using projected by (simp only: lpc_seg_reinterface_sound)
  show ?thesis by (rule lpc_return_contract_start[OF entry renamed])
qed

end
