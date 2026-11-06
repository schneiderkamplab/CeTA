theory LP_Prolog_Helper_Prefix_Steps
  imports LP_Prolog_Helper_Prefix_Check
begin

lemma lpp_checked_helper_site_steps:
  assumes checked: "lpp_check_helper_site P H K s"
    and ctx: "lpp_caller_numeric_context H K rho eta names"
    and guards: "lpp_helper_site_guards s rho"
  shows "lpp_caller_numeric_context H (lpphs_output s#K)
      (rho(lpphs_output s:=lpp_helper_site_value s rho))
      (lpp_helper_caller_environment eta (names (lpphs_output s)) (lpp_helper_site_value s rho))
      (\<lambda>y. CHR ''0''#names y) \<and>
    (\<exists>mark. (LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
        (lpp_helper_operation_goal (LPPHCall s)#rest) @ pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
        (lpp_helper_caller_environment eta (names (lpphs_output s)) (lpp_helper_site_value s rho)))) rest @
        map (lp_cut_map (\<lambda>t. lp_isubst t
          (lpc_fresh_caller(names (lpphs_output s):=lpp_integer_value (lpp_helper_site_value s rho))))) pending)#
        LPCBarrier mark#saved)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+)"
proof -
  let ?r = "lpphs_recipe s"
  let ?ns = "lpp_helper_site_arguments s rho"
  let ?x = "lpphs_output s"
  have recipe: "lpp_check_helper_return_recipe P ?r"
    and interface: "lpp_check_helper_call_interface ?r (lpphs_positions s) (lpphs_output_position s)"
    and numeric_length: "length (lpphr_head ?r)=length ?ns"
    and local_fresh: "?x\<notin>set H" and unknown: "?x\<notin>set K"
    using checked by (auto simp: lpp_check_helper_site_def lpp_helper_site_arguments_def)
  have observed: "lpp_partial_observations (lpphs_positions s) ?ns
    (map (\<lambda>t. lp_ieval t eta) (lpphs_terms s))"
    by (rule lpp_helper_site_observations[OF checked ctx])
  have bound: "lpphs_output_position s<length (lpphs_terms s)"
    using checked interface by (auto simp: lpp_check_helper_site_def lpp_check_helper_call_interface_def)
  have fresh: "(map (\<lambda>t. lp_ieval t eta) (lpphs_terms s))!lpphs_output_position s=LPIVar (names ?x)"
    using ctx local_fresh unknown checked bound
    by (auto simp: lpp_caller_numeric_context_def lpp_check_helper_site_def)
  have holds: "lpp_recurrence_guards (lpphr_prefix ?r)
    (lpp_recurrence_arguments (lpphr_head ?r) ?ns)"
    using guards by (simp add: lpp_helper_site_guards_def lpp_helper_site_environment_def)
  note source = lpp_helper_caller_body_return[OF recipe interface numeric_length observed fresh holds,
    where n="lpp_helper_site_value s rho" and rest=rest and pending=pending and saved=saved]
  have typed: "lpp_caller_numeric_context H (?x#K) (rho(?x:=lpp_helper_site_value s rho))
    (lpp_helper_caller_environment eta (names ?x) (lpp_helper_site_value s rho)) (\<lambda>y. CHR ''0''#names y)"
    by (rule lpp_caller_numeric_helper[OF ctx local_fresh unknown])
  show ?thesis using typed source
    by (simp add: lpp_helper_site_value_def lpp_helper_site_environment_def)
qed

ML \<open>
val checked = [@{thm lpp_checked_helper_site_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted checked helper source step" else ();
\<close>
end
