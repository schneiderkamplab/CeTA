theory LP_Prolog_Helper_Prefix_Failure
  imports LP_Prolog_Helper_Prefix_Sequence
begin

lemma lpp_source_barriers_restore:
  assumes barriers: "lp_cut_barriers bars"
  shows "(bars@saved,saved)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
  using barriers
proof (induct bars)
  case Nil show ?case by simp
next
  case (Cons b bars)
  obtain mark where b: "b=LPCBarrier mark" using Cons.prems by (cases b) auto
  have admin: "(LPCBarrier mark#bars@saved,bars@saved)\<in>lp_cut_mgu_source P"
    by (rule lp_cut_mgu_source.admin) simp
  have step: "(LPCBarrier mark#bars@saved,bars@saved)\<in>lpp_builtin_source P lpp_integer_source_builtin"
    using admin by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  have tail_bars: "lp_cut_barriers bars" using Cons.prems by simp
  note tail = Cons.hyps[OF tail_bars]
  show ?case using rtrancl_trans[OF r_into_rtrancl[OF step] tail] by (simp only: b append_Cons)
qed

lemma lpp_checked_helper_prefix_failure:
  assumes checked: "lpp_check_helper_prefix P H K ops"
    and ctx: "lpp_caller_numeric_context H K rho eta names"
    and guards: "lpp_helper_prefix_guards ops rho"
    and descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_expression_check (lpp_helper_prefix_known K ops) a"
    and right: "lpp_expression_check (lpp_helper_prefix_known K ops) b"
    and fails: "\<not>lpp_integer_compare c
      (lpp_expression_value (if reversed then b else a) (lpp_helper_prefix_values ops rho))
      (lpp_expression_value (if reversed then a else b) (lpp_helper_prefix_values ops rho))"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
      (map lpp_helper_operation_goal ops @ lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest) @ pending)#saved,
    saved)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?K = "lpp_helper_prefix_known K ops"
  let ?rho = "lpp_helper_prefix_values ops rho"
  obtain next_eta next_names next_pending bars where final_ctx:
      "lpp_caller_numeric_context H ?K ?rho next_eta next_names"
    and bars: "lp_cut_barriers bars"
    and prefix: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
        (map lpp_helper_operation_goal ops @ lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest) @ pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t next_eta))
        (lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest) @ next_pending)#(bars@saved))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    using lpp_checked_helper_prefix_steps[OF checked ctx guards,
      where rest="lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest" and pending=pending and saved=saved] by blast
  have known: "next_eta y=lpp_integer_value (?rho y)" if "y\<in>set ?K" for y
    using final_ctx that by (simp add: lpp_caller_numeric_context_def)
  have guard: "\<not>lpp_integer_compare c
    (if reversed then lpp_expression_value b ?rho else lpp_expression_value a ?rho)
    (if reversed then lpp_expression_value a ?rho else lpp_expression_value b ?rho)"
    using fails by (cases reversed) simp_all
  note failure = lpp_integer_recurrence_comparison_failure[OF descriptor
    lpp_expression_evaluation[OF left known] lpp_expression_evaluation[OF right known] guard,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t next_eta)) rest @ next_pending" and es="bars@saved" and P=P]
  have failed: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t next_eta))
      (lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest) @ next_pending)#(bars@saved),bars@saved)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using failure by simp
  note restore = lpp_source_barriers_restore[OF bars, where saved=saved and P=P]
  show ?thesis using prefix failed restore
    by (meson r_into_trancl rtrancl_trancl_trancl trancl_rtrancl_trancl)
qed

ML \<open>
val checked = [@{thm lpp_source_barriers_restore}, @{thm lpp_checked_helper_prefix_failure}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper prefix failure coverage" else ();
\<close>
end
