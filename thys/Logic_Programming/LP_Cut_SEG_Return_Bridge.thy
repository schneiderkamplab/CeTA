theory LP_Cut_SEG_Return_Bridge
  imports LP_Cut_SEG_Roles LP_Cut_SEG_Captured
begin

text \<open>A checked return rule bridges the actual child answer to the
parent answer. The continuation stores entry values; the actual answer may
instantiate other variables but cannot change these captured ground values.
No inverse instance substitution or guessed answer is used.\<close>

theorem lpc_seg_checked_actual_step:
  assumes checked: "lpc_seg_check_encoded_pair 2 target_depth is_cont c d C R
      (Fun u (child_out#captured)) parent_out"
    and cont: "is_cont u"
    and actual: "lpc_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and child_vars: "vars_term child_out \<subseteq> set vs"
    and parent_vars: "vars_term parent_out \<subseteq> set vs"
    and child_finite: "lp_seg_ground (lp_ieval (lpc_seg_position_template vs child_out) rho)"
    and captured_finite: "list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) captured"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "((More (c u) [] \<box>
      (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) captured))
        \<langle>lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d
          (lp_ieval (lpc_seg_position_template vs child_out) rho))\<rangle>,
      lpc_seg_finite_value (lpc_seg_role_value target_depth is_cont c d
        (lp_ieval (lpc_seg_position_template vs parent_out) rho)))\<in>qrstep False Q R"
proof -
  obtain theta where source: "lpc_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpc_seg_observed_actual[OF actual] by blast
  have child_equal: "lp_ieval (lpc_seg_position_template vs child_out) rho = lp_ieval child_out theta"
    unfolding rho by (rule lpc_seg_position_eval[OF distinct child_vars])
  have parent_equal: "lp_ieval (lpc_seg_position_template vs parent_out) rho = lp_ieval parent_out theta"
    unfolding rho by (rule lpc_seg_position_eval[OF distinct parent_vars])
  have captured_equal: "lp_ieval t theta=lp_ieval t eta" if member: "t\<in>set captured" for t
  proof (rule lpc_seg_captured_term[OF source])
    show "\<forall>x\<in>vars_term t. lp_seg_ground (eta x)"
      using captured_finite member by (auto simp: list_all_iff lp_seg_ground_eval)
    show "list_all (\<lambda>e. \<forall>x\<in>vars_term t. snd e x=eta x)
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]" by simp
  qed
  have first: "lp_seg_ground (lp_ieval child_out theta)" using child_finite child_equal by simp
  have rest: "list_all lp_seg_ground (map (\<lambda>t. lp_ieval t theta) captured)"
    using captured_finite captured_equal by (auto simp: list_all_iff)
  have finite: "lp_seg_ground (lp_ieval (Fun u (child_out#captured)) theta)"
    using first rest by simp
  have step: "(lpc_seg_finite_value (lpc_seg_role_value 2 is_cont c d
        (lp_ieval (Fun u (child_out#captured)) theta)),
      lpc_seg_finite_value (lpc_seg_role_value target_depth is_cont c d (lp_ieval parent_out theta)))\<in>qrstep False Q R"
    by (rule lpc_seg_checked_encoded_pair[OF checked finite range roots])
  have equal: "lpc_seg_finite_value (lpc_seg_role_value 2 is_cont c d
        (lp_ieval (Fun u (child_out#captured)) theta)) =
      (More (c u) [] \<box>
        (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) captured))
        \<langle>lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lp_ieval child_out theta))\<rangle>"
    using lpc_seg_role_continuation_context[where is_cont=is_cont and u=u and n=1 and c=c and d=d, OF cont first rest]
    by (simp add: numeral_eq_Suc map_map captured_equal cong: map_cong)
  show ?thesis using step by (simp only: equal child_equal parent_equal)
qed

lemmas lpc_seg_checked_actual_return = lpc_seg_checked_actual_step[where target_depth=1]

definition lpc_seg_check_return_ground where
  "lpc_seg_check_return_ground (P::('f,string) lp_cut_program) pre G vs
      (t::('f lp_cut_symbol,string) term) Q Fs modes =
    lpc_check_return_output_groundness P pre G (map Var vs :: ('f lp_cut_symbol,string) term list)
      (vars_term_list (lpc_seg_position_template vs t)) Q Fs modes"

lemma lpc_seg_checked_return_ground:
  assumes checked: "lpc_seg_check_return_ground P pre G vs t Q Fs modes"
    and known: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "lp_seg_ground (lp_ieval (lpc_seg_position_template vs t) rho)"
proof -
  have ground: "\<forall>i\<in>set (vars_term_list (lpc_seg_position_template vs t)). lp_seg_ground (rho i)"
    by (rule lpc_return_output_groundness_sound[OF _ known actual])
      (use checked in \<open>simp add: lpc_seg_check_return_ground_def\<close>)
  show ?thesis using ground by (simp add: lp_seg_ground_eval)
qed

end
