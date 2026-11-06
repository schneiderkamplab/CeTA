theory LP_Prolog_Partial_Integer_Prefix
  imports LP_Prolog_Partial_Integer_Body
begin

lemma lpp_partial_initial_environment:
  assumes observed_head: "\<And>x. x\<in>set K \<Longrightarrow> x\<in>set H"
    and observed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lpc_fresh_head_environment H eta = lpp_partial_environment H K rho eta"
  using observed_head observed
  by (intro ext) (auto simp: lpc_fresh_head_environment_def lpp_partial_environment_def lpp_integer_value_def)

lemma lpp_partial_guard_step:
  assumes descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_expression_check K a" and right: "lpp_expression_check K b"
    and holds: "lpp_integer_compare c (lpp_expression_value (if reversed then b else a) rho)
      (lpp_expression_value (if reversed then a else b) rho)"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_partial_environment H K rho eta)))
        (lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest) @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_partial_environment H K rho eta))) rest @ map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  let ?eta = "lpp_partial_environment H K rho eta"
  have guard: "lpp_integer_compare c (if reversed then lpp_expression_value b rho else lpp_expression_value a rho)
      (if reversed then lpp_expression_value a rho else lpp_expression_value b rho)"
    using holds by (cases reversed) auto
  note step = lpp_integer_recurrence_comparison_success[OF descriptor
    lpp_partial_expression_evaluation[OF left] lpp_partial_expression_evaluation[OF right] guard,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t ?eta)) rest @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending" and es=es and P=P]
  show ?thesis using step by simp
qed

lemma lpp_partial_body_source_steps:
  assumes checked: "lpp_partial_recurrence_check H K ops" and holds: "lpp_recurrence_guards ops rho"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_partial_environment H K rho eta)))
        (map lpp_recurrence_goal ops @ rest) @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
        (lpp_partial_environment H (lpp_recurrence_known K ops) (lpp_recurrence_values ops rho) eta))) rest @ map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
  using checked holds
proof (induct ops arbitrary: K rho)
  case Nil then show ?case by simp
next
  case (Cons op ops)
  show ?case
  proof (cases op)
    case (LPPRSet x e)
    have head_fresh: "x\<notin>set H" and fresh: "x\<notin>set K" and expression: "lpp_expression_check K e"
      and tail_check: "lpp_partial_recurrence_check H (x#K) ops"
      and tail_guards: "lpp_recurrence_guards ops (rho(x:=lpp_expression_value e rho))"
      using Cons.prems by (auto simp: LPPRSet)
    note step = lpp_partial_assignment_step[OF head_fresh fresh expression,
      where rest="map lpp_recurrence_goal ops @ rest" and es=es and P=P and rho=rho and pending=pending and eta=eta]
    note tail = Cons.hyps[OF tail_check tail_guards]
    show ?thesis using rtrancl_trans[OF r_into_rtrancl[OF step] tail]
      by (simp only: LPPRSet list.map append_Cons lpp_recurrence_known.simps lpp_recurrence_values.simps)
  next
    case (LPPRGuard f c reversed a b)
    have descriptor: "lpp_comparison_descriptor f c reversed"
      and left: "lpp_expression_check K a" and right: "lpp_expression_check K b"
      and guard: "lpp_integer_compare c (lpp_expression_value (if reversed then b else a) rho)
        (lpp_expression_value (if reversed then a else b) rho)"
      and tail_check: "lpp_partial_recurrence_check H K ops" and tail_guards: "lpp_recurrence_guards ops rho"
      using Cons.prems by (auto simp: LPPRGuard)
    note step = lpp_partial_guard_step[OF descriptor left right guard,
      where rest="map lpp_recurrence_goal ops @ rest" and es=es and P=P and pending=pending and eta=eta]
    note tail = Cons.hyps[OF tail_check tail_guards]
    show ?thesis using rtrancl_trans[OF r_into_rtrancl[OF step] tail]
      by (simp only: LPPRGuard list.map append_Cons lpp_recurrence_known.simps lpp_recurrence_values.simps)
  qed
qed


ML \<open>
val checked = [@{thm lpp_partial_initial_environment}, @{thm lpp_partial_body_source_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial arithmetic prefix dependency" else ();
\<close>
end
