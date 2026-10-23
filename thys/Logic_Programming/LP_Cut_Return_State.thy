theory LP_Cut_Return_State
  imports LP_Cut_Return_Resolution
begin

text \<open>A finite return interface denotes a total environment. Outside
the interface we use a ground constant, so source substitutions commute with
the representation. Only listed continuation variables may be observed.\<close>

definition lpc_return_env where
  "lpc_return_env ts eta n = (if n < length ts then lp_ieval (ts!n) eta
    else LPIFun LPCTruth [])"

definition lpc_return_eval where
  "lpc_return_eval eta ss = map
    (\<lambda>(e,ts). (lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e, lpc_return_env ts eta)) ss"

lemma lpc_return_env_cong:
  "map (\<lambda>t. lp_ieval t eta) ts = map (\<lambda>t. lp_ieval t nu) us \<Longrightarrow>
    lpc_return_env ts eta = lpc_return_env us nu"
  unfolding lpc_return_env_def
  by (rule ext) (metis length_map nth_map)

lemma lpc_return_env_active:
  assumes "map (\<lambda>t. lp_ieval t nu) us = map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) ts"
  shows "lpc_return_env us nu = (\<lambda>n. lp_isubst (lpc_return_env ts eta n) sigma)"
proof (rule ext)
  fix n
  have len: "length us = length ts" using assms by (metis length_map)
  show "lpc_return_env us nu n = lp_isubst (lpc_return_env ts eta n) sigma"
    using assms len by (auto simp: lpc_return_env_def dest: arg_cong[where f="\<lambda>xs. xs!n"])
qed

lemma lpc_return_eval_erases:
  "map fst (lpc_return_eval eta ss) = lp_cut_state_eval (map fst ss) eta"
  by (simp add: lpc_return_eval_def lp_cut_state_map_def map_map o_def split_def)

lemma lpc_return_eval_admin:
  "lpc_return_admin (lpc_return_eval eta ss) =
    map_option (map_prod (map_option (\<lambda>ts. lpc_return_env ts eta))
      (lpc_return_eval eta)) (lpc_return_admin ss)"
  unfolding lpc_return_eval_def
  using lpc_return_admin_map[of "\<lambda>t. lp_ieval t eta" "\<lambda>ts. lpc_return_env ts eta" ss]
  by (simp add: map_prod_def split_def)

lemma lpc_return_eval_admin_sound:
  "lpc_return_admin ss = Some (event,tt) \<Longrightarrow>
    lpc_answer_transition P (lpc_return_eval eta ss)
      (map_option (\<lambda>ts. lpc_return_env ts eta) event) (lpc_return_eval eta tt)"
  by (rule lpc_return_admin_sound) (simp add: lpc_return_eval_admin)

definition lpc_return_short where
  "lpc_return_short k ss = (\<forall>(e,ts)\<in>set ss.
    lp_cut_short_entry k e \<and> (\<forall>t\<in>set ts. \<forall>x\<in>vars_term t. length x<k))"

lemma lpc_return_eval_saved:
  assumes short: "lpc_return_short k ss" and bounds: "k\<le>l"
  shows "lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ss = lpc_return_eval eta ss"
  unfolding lpc_return_eval_def
proof (rule map_cong[OF refl])
  fix frame assume "frame\<in>set ss"
  then obtain e ts where frame: "frame=(e,ts)"
    and e: "lp_cut_short_entry k e"
    and ts: "\<forall>t\<in>set ts. \<forall>x\<in>vars_term t. length x<k"
    using short by (cases frame) (auto simp: lpc_return_short_def)
  have entry: "lp_cut_entry_map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) e =
    lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e"
    by (rule lp_cut_resolution_saved_entry[OF e bounds])
  have env: "lpc_return_env ts (lp_cut_resolution_env k l eta sigma rho) = lpc_return_env ts eta"
    by (rule lpc_return_env_cong, rule map_cong[OF refl], rule lp_cut_resolution_old[OF _ bounds])
      (use ts in auto)
  show "(case frame of (e,ts) \<Rightarrow>
      (lp_cut_entry_map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) e,
       lpc_return_env ts (lp_cut_resolution_env k l eta sigma rho))) =
    (case frame of (e,ts) \<Rightarrow> (lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,lpc_return_env ts eta))"
    using entry env by (simp add: frame)
qed

end
