theory LP_Cut_Domain_SEG_Split_Bridge
 imports LP_Cut_Domain_SEG_Child
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_seg_actual_pair_finite:
  assumes checked: "lpc_seg_check_encoded_pair 2 target_depth is_cont c d C R
      (Fun u (child_out#captured)) next_term"
    and actual: "precise_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and child_vars: "vars_term child_out \<subseteq> set vs"
    and next_vars: "vars_term next_term \<subseteq> set vs"
    and child_finite: "lp_seg_ground (lp_ieval (lpc_seg_position_template vs child_out) rho)"
    and captured_finite: "list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) captured"
  shows "lp_seg_ground (lp_ieval (lpc_seg_position_template vs next_term) rho)"
proof -
  obtain theta where source: "precise_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    by (rule precise_seg_observed_actual[OF actual]) assumption
  have child_equal: "lp_ieval (lpc_seg_position_template vs child_out) rho=lp_ieval child_out theta"
    unfolding rho by (rule lpc_seg_position_eval[OF distinct child_vars])
  have next_equal: "lp_ieval (lpc_seg_position_template vs next_term) rho=lp_ieval next_term theta"
    unfolding rho by (rule lpc_seg_position_eval[OF distinct next_vars])
  have captured_equal: "lp_ieval t theta=lp_ieval t eta" if member: "t\<in>set captured" for t
  proof (rule precise_seg_captured_term[OF source])
    show "\<forall>x\<in>vars_term t. lp_seg_ground (eta x)"
      using captured_finite member by (auto simp: list_all_iff lp_seg_ground_eval)
    show "list_all (\<lambda>e. \<forall>x\<in>vars_term t. snd e x=eta x)
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]" by simp
  qed
  have finite: "lp_seg_ground (lp_ieval (Fun u (child_out#captured)) theta)"
    using child_finite child_equal captured_finite captured_equal
    by (auto simp: list_all_iff)
  show ?thesis unfolding next_equal by (rule lpc_seg_checked_pair_finite[OF checked finite])
qed


theorem precise_seg_checked_actual_continue:
  assumes checked: "lpc_seg_check_encoded_pair 2 2 is_cont c d C R
      (Fun u (child_out#captured)) (Fun v (next_in#next_captured))"
    and cont: "is_cont u" "is_cont v"
    and actual: "precise_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and child_vars: "vars_term child_out \<subseteq> set vs"
    and next_vars: "vars_term (Fun v (next_in#next_captured)) \<subseteq> set vs"
    and child_finite: "lp_seg_ground (lp_ieval (lpc_seg_position_template vs child_out) rho)"
    and captured_finite: "list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) captured"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "lp_seg_ground (lp_ieval (lpc_seg_position_template vs next_in) rho) \<and>
    list_all (\<lambda>t. lp_seg_ground (lp_ieval (lpc_seg_position_template vs t) rho)) next_captured \<and>
    ((More (c u) [] \<box>
      (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) captured))
      \<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs child_out) rho\<rangle>,
     (More (c v) [] \<box>
      (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id
        (lp_ieval (lpc_seg_position_template vs t) rho))) next_captured))
      \<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs next_in) rho\<rangle>)
      \<in>qrstep False Q R"
proof -
  have finite: "lp_seg_ground (lp_ieval (lpc_seg_position_template vs (Fun v (next_in#next_captured))) rho)"
    by (rule precise_seg_actual_pair_finite[OF checked actual distinct child_vars next_vars child_finite captured_finite])
  have first: "lp_seg_ground (lp_ieval (lpc_seg_position_template vs next_in) rho)"
    and rest: "list_all lp_seg_ground (map (\<lambda>t. lp_ieval (lpc_seg_position_template vs t) rho) next_captured)"
    using finite by (simp_all add: lpc_seg_position_template_def map_map o_def)
  have step: "((More (c u) [] \<box>
      (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) captured))
      \<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs child_out) rho\<rangle>,
    lpc_seg_finite_value (lpc_seg_role_value 2 is_cont c d
      (lp_ieval (lpc_seg_position_template vs (Fun v (next_in#next_captured))) rho)))\<in>qrstep False Q R"
    using precise_seg_checked_actual_step[where Q=Q, OF checked cont(1) actual distinct child_vars next_vars child_finite captured_finite range roots]
    by (simp only: lpc_seg_return_value_def)
  have equal: "lpc_seg_finite_value (lpc_seg_role_value 2 is_cont c d
      (lp_ieval (lpc_seg_position_template vs (Fun v (next_in#next_captured))) rho)) =
     (More (c v) [] \<box>
      (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id
        (lp_ieval (lpc_seg_position_template vs t) rho))) next_captured))
      \<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template vs next_in) rho\<rangle>"
    using lpc_seg_role_continuation_context[where is_cont=is_cont and u=v and n=1 and c=c and d=d,
      OF cont(2) first rest]
    by (simp add: lpc_seg_position_template_def lpc_seg_return_value_def numeral_eq_Suc map_map o_def)
  show ?thesis using first rest step by (simp add: equal list_all_iff)
qed


lemma precise_seg_return_ground_environment:
  assumes checked: "lpc_seg_check_return_ground P pre G vs (Fun LPCTruth (map Var H)) ground_program Fs modes"
    and known: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and actual: "precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
    and distinct: "distinct vs" and covered: "set H \<subseteq> set vs"
    and rho: "rho=lpc_return_env (map Var vs) theta"
  shows "\<forall>x\<in>set H. lp_seg_ground (theta x)"
proof -
  have finite: "lp_seg_ground (lp_ieval (lpc_seg_position_template vs (Fun LPCTruth (map Var H))) rho)"
    by (rule precise_seg_checked_return_ground[OF checked known actual])
  have equal: "lp_ieval (lpc_seg_position_template vs (Fun LPCTruth (map Var H))) rho =
    lp_ieval (Fun LPCTruth (map Var H)) theta"
    unfolding rho by (rule lpc_seg_position_eval[OF distinct]) (use covered in auto)
  show ?thesis using finite by (simp add: equal list_all_iff)
qed


end
end
