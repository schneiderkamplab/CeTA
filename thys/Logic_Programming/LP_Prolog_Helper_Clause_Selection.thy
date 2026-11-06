theory LP_Prolog_Helper_Clause_Selection
  imports LP_Prolog_Helper_Prefix_Failure
begin

lemma lpp_helper_bind_goal:
  "lp_cut_bind mark h (lpp_helper_operation_goal op)=lp_cut_map h (lpp_helper_operation_goal op)"
  by (cases op) (simp_all add: lpp_recurrence_bind_goal)

lemma lpp_helper_selected_clause_failure:
  assumes index: "d<length P"
    and clause: "P!d=(Fun (LPCUser f) (map Var H),
      map lpp_helper_operation_goal ops @ lpp_recurrence_goal (LPPRGuard g c reversed a b)#rest)"
    and observed_head: "\<And>x. x\<in>set K \<Longrightarrow> x\<in>set H"
    and observed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
    and checked: "lpp_check_helper_prefix P H K ops"
    and prefix_holds: "lpp_helper_prefix_guards ops rho"
    and descriptor: "lpp_comparison_descriptor g c reversed"
    and left: "lpp_expression_check (lpp_helper_prefix_known K ops) a"
    and right: "lpp_expression_check (lpp_helper_prefix_known K ops) b"
    and fails: "\<not>lpp_integer_compare c
      (lpp_expression_value (if reversed then b else a) (lpp_helper_prefix_values ops rho))
      (lpp_expression_value (if reversed then a else b) (lpp_helper_prefix_values ops rho))"
  shows "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark#es,es)
    \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?env = "lpp_partial_environment H K rho eta"
  let ?call = "lp_ieval (Fun (LPCUser f) (map Var H)) eta"
  let ?body = "map lpp_helper_operation_goal ops @ lpp_recurrence_goal (LPPRGuard g c reversed a b)#rest"
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
  have ctx: "lpp_caller_numeric_context H K rho ?env (\<lambda>y. CHR ''1''#y)"
    by (rule lpp_caller_numeric_initial)
  have failure: "(LPCGoals (map (lp_cut_bind mark ?h) ?body @ ?pending)#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_checked_helper_prefix_failure[
      OF checked ctx prefix_holds descriptor left right fails,
      where rest="map (lp_cut_bind mark id) rest" and saved=es and pending="?pending"]
    by (simp add: map_map lp_cut_map_bind lpp_recurrence_bind_goal lpp_helper_bind_goal o_def)
  show ?thesis using source_resolution failure by (meson r_into_trancl trancl_trans)
qed

end
