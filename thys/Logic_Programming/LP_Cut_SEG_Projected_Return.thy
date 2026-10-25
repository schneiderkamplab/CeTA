theory LP_Cut_SEG_Projected_Return
  imports LP_Cut_SEG_Projected_Context
begin

lemma lpc_seg_encoded_capture_step:
  fixes filtering :: "'g afs" and v :: "('g,string) term"
  assumes step: "lpc_answer_transition P ss event us"
    and known: "list_all (\<lambda>e. lp_iproject filtering
      (map_lp_iterm d id (lp_ieval t (snd e))) v) ss"
  shows "list_all (\<lambda>e. lp_iproject filtering
      (map_lp_iterm d id (lp_ieval t (snd e))) v) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> lp_iproject filtering
      (map_lp_iterm d id (lp_ieval t eta)) v)"
  using step known
  by (cases rule: lpc_answer_transition.cases)
    (auto simp: list_all_iff lp_ieval_subst[symmetric] lp_data_map_subst
      intro: lp_iproject_subst dest: subsetD[OF lpc_answer_prune_set_subset])

lemma lpc_seg_encoded_capture_actual:
  fixes filtering :: "'g afs" and v :: "('g,string) term"
  assumes actual: "lpc_actual_return P ss eta"
    and known: "list_all (\<lambda>e. lp_iproject filtering
      (map_lp_iterm d id (lp_ieval t (snd e))) v) ss"
  shows "lp_iproject filtering (map_lp_iterm d id (lp_ieval t eta)) v"
proof -
  obtain us tail where path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some eta) tail"
    using actual by (auto simp: lpc_actual_return_def)
  have preserved: "list_all (\<lambda>e. lp_iproject filtering
      (map_lp_iterm d id (lp_ieval t (snd e))) v) us"
    using path known
    by (induct rule: rtrancl_induct)
      (auto simp: lpc_answer_steps_def dest: lpc_seg_encoded_capture_step)
  show ?thesis using lpc_seg_encoded_capture_step[OF event preserved] by simp
qed

lemma lpc_seg_encoded_capture_observed:
  fixes filtering :: "'g afs" and v :: "('g,string) term"
  assumes actual: "lpc_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and vars: "vars_term t \<subseteq> set vs"
    and observed: "lp_iproject filtering (map_lp_iterm d id (lp_ieval t eta)) v"
  shows "lp_iproject filtering
    (map_lp_iterm d id (lp_ieval (lpc_seg_position_template vs t) rho)) v"
proof -
  obtain theta where source: "lpc_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpc_seg_observed_actual[OF actual] by blast
  have preserved: "lp_iproject filtering (map_lp_iterm d id (lp_ieval t theta)) v"
    by (rule lpc_seg_encoded_capture_actual[OF source]) (simp add: observed)
  show ?thesis unfolding rho
    by (simp only: lpc_seg_position_eval[OF distinct vars] preserved)
qed

theorem lpc_seg_projected_actual_step:
  fixes filtering :: "'g afs" and ms :: "('g,string) term list"
    and n :: "('g,string) term"
  assumes checked: "lpc_seg_check_projected_pair filtering 2 target_depth is_cont c d R
      (Fun u (child_out#captured)) parent_out"
    and cont: "is_cont u"
    and actual: "lpc_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and child_vars: "vars_term child_out \<subseteq> set vs"
    and parent_vars: "vars_term parent_out \<subseteq> set vs"
    and af: "afs filtering (c u,Suc (length captured)) = AFList (0#map Suc indices)"
    and captured_pr: "list_all2 (\<lambda>i m. i<length captured \<and>
      lp_iproject filtering (map_lp_iterm d id (lp_ieval (captured!i) eta)) m) indices ms"
    and child_pr: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d
      (lp_ieval (lpc_seg_position_template vs child_out) rho)) n"
  shows "(LPIFun (c u) (lpc_seg_role_value 1 is_cont c d
      (lp_ieval (lpc_seg_position_template vs child_out) rho)#
        map (\<lambda>t. map_lp_iterm d id (lp_ieval t eta)) captured),
      lpc_seg_role_value target_depth is_cont c d
        (lp_ieval (lpc_seg_position_template vs parent_out) rho))\<in>lpc_seg_projected_rel filtering R"
proof -
  obtain theta where source: "lpc_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpc_seg_observed_actual[OF actual] by blast
  have child_eq: "lp_ieval (lpc_seg_position_template vs child_out) rho = lp_ieval child_out theta"
    unfolding rho by (rule lpc_seg_position_eval[OF distinct child_vars])
  have parent_eq: "lp_ieval (lpc_seg_position_template vs parent_out) rho = lp_ieval parent_out theta"
    unfolding rho by (rule lpc_seg_position_eval[OF distinct parent_vars])
  have preserved: "lp_iproject filtering (map_lp_iterm d id (lp_ieval t theta)) v"
    if pr: "lp_iproject filtering (map_lp_iterm d id (lp_ieval t eta)) v"
    for t and v :: "('g,string) term"
    by (rule lpc_seg_encoded_capture_actual[OF source]) (simp add: pr)
  let ?caps = "\<lambda>nu. map (\<lambda>t. map_lp_iterm d id (lp_ieval t nu)) captured"
  have old: "list_all2 (\<lambda>i m. i<length (?caps eta) \<and>
      lp_iproject filtering (?caps eta!i) m) indices ms"
    using captured_pr by (auto simp: list_all2_conv_all_nth)
  have fresh: "list_all2 (\<lambda>i m. i<length (?caps theta) \<and>
      lp_iproject filtering (?caps theta!i) m) indices ms"
    using captured_pr preserved by (auto simp: list_all2_conv_all_nth)
  have old_af: "afs filtering (c u,Suc (length (?caps eta))) = AFList (0#map Suc indices)"
    and fresh_af: "afs filtering (c u,Suc (length (?caps theta))) = AFList (0#map Suc indices)"
    using af by simp_all
  have child: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lp_ieval child_out theta)) n"
    using child_pr child_eq by simp
  have left: "lp_iproject filtering
    (LPIFun (c u) (lpc_seg_role_value 1 is_cont c d (lp_ieval child_out theta)#?caps eta))
    (Fun (c u) (n#ms))"
    by (rule lpc_seg_projected_pending[OF old_af old child])
  have current: "lp_iproject filtering
    (lpc_seg_role_value 2 is_cont c d (lp_ieval (Fun u (child_out#captured)) theta))
    (Fun (c u) (n#ms))"
  proof -
    have two: "(2::nat)=Suc 1" by simp
    show ?thesis using lpc_seg_projected_pending[OF fresh_af fresh child]
      by (simp only: two lp_ieval.simps list.map
        lpc_seg_role_continuation[where is_cont=is_cont and u=u and n=1 and c=c and d=d, OF cont]
        map_map o_def)
  qed
  obtain result where right: "lp_iproject filtering
      (lpc_seg_role_value target_depth is_cont c d (lp_ieval parent_out theta)) result"
    and step: "(Fun (c u) (n#ms),result)\<in>rstep (af_rule filtering ` R)"
    by (rule lpc_seg_checked_projected_pair[OF checked current]) blast
  show ?thesis using left right step
    by (auto simp: lpc_seg_projected_rel_def child_eq parent_eq)
qed

lemmas lpc_seg_projected_actual_return = lpc_seg_projected_actual_step[where target_depth=1]

end
