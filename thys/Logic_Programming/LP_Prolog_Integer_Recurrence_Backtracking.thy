theory LP_Prolog_Integer_Recurrence_Backtracking
  imports LP_Prolog_Integer_Recurrence_Iteration
begin

text \<open>A failed arithmetic prefix resumes the original alternative stack.
Fresh assignments in that prefix do not update the saved alternative, even
when its variable names also occur in the failed clause. This is a source
execution fact, not permission to remove a branch from a termination graph.\<close>

lemma lpp_recurrence_guard_failure_step:
  assumes descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_expression_check K a" and right: "lpp_expression_check K b"
    and fails: "\<not>lpp_integer_compare c (lpp_expression_value (if reversed then b else a) rho)
      (lpp_expression_value (if reversed then a else b) rho)"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_recurrence_environment K rho)))
        (lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest))#es,es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  let ?eta = "lpp_recurrence_environment K rho"
  have guard: "\<not>lpp_integer_compare c (if reversed then lpp_expression_value b rho else lpp_expression_value a rho)
      (if reversed then lpp_expression_value a rho else lpp_expression_value b rho)"
    using fails by (cases reversed) auto
  note step = lpp_integer_recurrence_comparison_failure[OF descriptor
    lpp_recurrence_expression_evaluation[OF left] lpp_recurrence_expression_evaluation[OF right] guard,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t ?eta)) rest" and es=es and P=P]
  show ?thesis using step by simp
qed

lemma lpp_recurrence_failed_prefix_restores_alternatives:
  assumes checked: "lpp_recurrence_check K ops"
    and prefix_holds: "lpp_recurrence_guards ops rho"
    and descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_expression_check (lpp_recurrence_known K ops) a"
    and right: "lpp_expression_check (lpp_recurrence_known K ops) b"
    and fails: "\<not>lpp_integer_compare c
      (lpp_expression_value (if reversed then b else a) (lpp_recurrence_values ops rho))
      (lpp_expression_value (if reversed then a else b) (lpp_recurrence_values ops rho))"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_recurrence_environment K rho)))
        (map lpp_recurrence_goal ops @ lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest))#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  note prefix = lpp_recurrence_body_source_steps[OF checked prefix_holds,
    where rest="lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest" and es=es and P=P]
  note failure = lpp_recurrence_guard_failure_step[OF descriptor left right fails,
    where rest=rest and es=es and P=P]
  show ?thesis using prefix failure
    by (meson rtrancl_trancl_trancl r_into_trancl)
qed


lemma lpp_recurrence_selected_clause_failure:
  assumes index: "d<length P"
    and clause: "P!d=(Fun (LPCUser f) (map Var xs),
      map lpp_recurrence_goal ops @ lpp_recurrence_goal (LPPRGuard g c reversed a b)#rest)"
    and checked: "lpp_recurrence_check xs ops"
    and prefix_holds: "lpp_recurrence_guards ops rho"
    and descriptor: "lpp_comparison_descriptor g c reversed"
    and left: "lpp_expression_check (lpp_recurrence_known xs ops) a"
    and right: "lpp_expression_check (lpp_recurrence_known xs ops) b"
    and fails: "\<not>lpp_integer_compare c
      (lpp_expression_value (if reversed then b else a) (lpp_recurrence_values ops rho))
      (lpp_expression_value (if reversed then a else b) (lpp_recurrence_values ops rho))"
  shows "(LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
      (lpp_recurrence_environment xs rho))] d mark#es,es)
    \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?eta = "lpp_recurrence_environment xs rho"
  let ?call = "lp_ieval (Fun (LPCUser f) (map Var xs)) ?eta"
  let ?body = "map lpp_recurrence_goal ops @ lpp_recurrence_goal (LPPRGuard g c reversed a b)#rest"
  let ?h = "\<lambda>t. lp_ieval t ?eta"
  have ground: "lp_seg_ground (?eta x)" if "x\<in>set xs" for x
    using that by (auto simp: lpp_recurrence_environment_def lpp_integer_value_def intro: lp_seg_ground.intros)
  have fresh: "?eta x=LPIVar x" if "x\<notin>set xs" for x
    using that by (simp add: lpp_recurrence_environment_def)
  have mgu: "lpc_mgu_resolve ?call [] (fst (P!d)) (snd (P!d)) LPIVar ?eta"
    using lpc_ground_head_fresh_body_mgu[where f="LPCUser f" and bs="?body", OF ground fresh]
    by (simp add: clause)
  have resolution: "(LPCClause [LPCAtom ?call] d mark#es,
      LPCGoals (map (lp_cut_bind mark ?h) ?body)#es)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.resolve[OF index mgu, of mark es] by (simp add: clause)
  have source_resolution: "(LPCClause [LPCAtom ?call] d mark#es,
      LPCGoals (map (lp_cut_bind mark ?h) ?body)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using resolution by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  have failure: "(LPCGoals (map (lp_cut_bind mark ?h) ?body)#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_recurrence_failed_prefix_restores_alternatives[
      OF checked prefix_holds descriptor left right fails,
      where rest="map (lp_cut_bind mark id) rest" and es=es and P=P]
    by (simp add: map_map lp_cut_map_bind lpp_recurrence_bind_goal o_def)
  show ?thesis using source_resolution failure by (meson r_into_trancl trancl_trans)
qed

ML \<open>
val checked = [@{thm lpp_recurrence_guard_failure_step},
  @{thm lpp_recurrence_failed_prefix_restores_alternatives},
  @{thm lpp_recurrence_selected_clause_failure}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted arithmetic backtracking dependency" else ();
\<close>
end
