theory LP_Prolog_Partial_Integer_Failure
  imports LP_Prolog_Partial_Integer_Prefix LP_Prolog_Integer_Recurrence_Backtracking
begin

lemma lpp_partial_guard_failure_step:
  assumes descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_expression_check K a" and right: "lpp_expression_check K b"
    and fails: "\<not>lpp_integer_compare c (lpp_expression_value (if reversed then b else a) rho)
      (lpp_expression_value (if reversed then a else b) rho)"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_partial_environment H K rho eta)))
        (lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest) @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  let ?eta = "lpp_partial_environment H K rho eta"
  have guard: "\<not>lpp_integer_compare c (if reversed then lpp_expression_value b rho else lpp_expression_value a rho)
      (if reversed then lpp_expression_value a rho else lpp_expression_value b rho)"
    using fails by (cases reversed) auto
  note step = lpp_integer_recurrence_comparison_failure[OF descriptor
    lpp_partial_expression_evaluation[OF left] lpp_partial_expression_evaluation[OF right] guard,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t ?eta)) rest @
      map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending" and es=es and P=P]
  show ?thesis using step by simp
qed

lemma lpp_partial_failed_prefix_restores_alternatives:
  assumes checked: "lpp_partial_recurrence_check H K ops"
    and prefix_holds: "lpp_recurrence_guards ops rho"
    and descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_expression_check (lpp_recurrence_known K ops) a"
    and right: "lpp_expression_check (lpp_recurrence_known K ops) b"
    and fails: "\<not>lpp_integer_compare c
      (lpp_expression_value (if reversed then b else a) (lpp_recurrence_values ops rho))
      (lpp_expression_value (if reversed then a else b) (lpp_recurrence_values ops rho))"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_partial_environment H K rho eta)))
        (map lpp_recurrence_goal ops @ lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest) @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  note prefix = lpp_partial_body_source_steps[OF checked prefix_holds,
    where rest="lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest" and es=es and P=P and eta=eta and pending=pending]
  note failure = lpp_partial_guard_failure_step[OF descriptor left right fails,
    where rest=rest and es=es and P=P and H=H and eta=eta and pending=pending]
  show ?thesis using prefix failure
    by (meson rtrancl_trancl_trancl r_into_trancl)
qed



lemma lpp_partial_selected_clause_failure:
  assumes index: "d<length P"
    and clause: "P!d=(Fun (LPCUser f) (map Var H),
      map lpp_recurrence_goal ops @ lpp_recurrence_goal (LPPRGuard g c reversed a b)#rest)"
    and observed_head: "\<And>x. x\<in>set K \<Longrightarrow> x\<in>set H"
    and observed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
    and checked: "lpp_partial_recurrence_check H K ops"
    and prefix_holds: "lpp_recurrence_guards ops rho"
    and descriptor: "lpp_comparison_descriptor g c reversed"
    and left: "lpp_expression_check (lpp_recurrence_known K ops) a"
    and right: "lpp_expression_check (lpp_recurrence_known K ops) b"
    and fails: "\<not>lpp_integer_compare c
      (lpp_expression_value (if reversed then b else a) (lpp_recurrence_values ops rho))
      (lpp_expression_value (if reversed then a else b) (lpp_recurrence_values ops rho))"
  shows "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark#es,es)
    \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?env = "lpp_partial_environment H K rho eta"
  let ?call = "lp_ieval (Fun (LPCUser f) (map Var H)) eta"
  let ?body = "map lpp_recurrence_goal ops @ lpp_recurrence_goal (LPPRGuard g c reversed a b)#rest"
  let ?h = "\<lambda>t. lp_ieval t ?env"
  let ?pending = "map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending"
  have initial: "lpc_fresh_head_environment H eta=?env"
    by (rule lpp_partial_initial_environment[OF observed_head observed])
  have mgu: "lpc_mgu_resolve ?call pending (fst (P!d)) (snd (P!d)) lpc_fresh_caller ?env"
    using lpc_fresh_head_mgu[where eta=eta and f="LPCUser f" and xs=H and gs=pending and bs="?body"]
    by (simp add: clause initial)
  have resolution: "(LPCClause (LPCAtom ?call#pending) d mark#es,
      LPCGoals (map (lp_cut_bind mark ?h) ?body @ ?pending)#es)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.resolve[OF index mgu, of mark es] by (simp add: clause)
  have source_resolution: "(LPCClause (LPCAtom ?call#pending) d mark#es,
      LPCGoals (map (lp_cut_bind mark ?h) ?body @ ?pending)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using resolution by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  have failure: "(LPCGoals (map (lp_cut_bind mark ?h) ?body @ ?pending)#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_partial_failed_prefix_restores_alternatives[
      OF checked prefix_holds descriptor left right fails,
      where rest="map (lp_cut_bind mark id) rest" and es=es and P=P and eta=eta and pending=pending]
    by (simp add: map_map lp_cut_map_bind lpp_recurrence_bind_goal o_def)
  show ?thesis using source_resolution failure by (meson r_into_trancl trancl_trans)
qed

ML \<open>
val checked = [@{thm lpp_partial_selected_clause_failure}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial arithmetic failure dependency" else ();
\<close>
end
