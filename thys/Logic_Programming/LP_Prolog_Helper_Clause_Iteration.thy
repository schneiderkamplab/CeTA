theory LP_Prolog_Helper_Clause_Iteration
  imports LP_Prolog_Helper_Clause_Selection
begin

lemma lpp_helper_selected_clause_iteration:
  assumes selection: "lp_cut_slice P (LPCUser f) (length H)=earlier@c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var H),map lpp_helper_operation_goal ops @ rest)"
    and ordinary: "(f,length H)\<notin>lpp_builtin_signature"
    and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
      (LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    and observed_head: "\<And>y. y\<in>set K \<Longrightarrow> y\<in>set H"
    and observed: "\<And>y. y\<in>set K \<Longrightarrow> eta y=lpp_integer_value (rho y)"
    and checked: "lpp_check_helper_prefix P H K ops"
    and guards: "lpp_helper_prefix_guards ops rho"
  shows "\<exists>mark next_eta next_names next_pending bars.
    lpp_caller_numeric_context H (lpp_helper_prefix_known K ops)
      (lpp_helper_prefix_values ops rho) next_eta next_names \<and> lp_cut_barriers bars \<and>
    (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending)#saved,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t next_eta)) rest @ next_pending)#
        (bars @ map (\<lambda>d. LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark) cs @
          LPCBarrier mark#saved))\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?call = "lp_ieval (Fun (LPCUser f) (map Var H)) eta"
  let ?env = "lpp_partial_environment H K rho eta"
  let ?pending = "map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending"
  have initial: "lpc_fresh_head_environment H eta=?env"
    by (rule lpp_partial_initial_environment[OF observed_head observed])
  obtain mark where selected: "(LPCGoals (LPCAtom ?call#pending)#saved,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?env))
        (map lpp_helper_operation_goal ops @ rest) @ ?pending)#
      (map (\<lambda>d. LPCClause (LPCAtom ?call#pending) d mark) cs @ LPCBarrier mark#saved))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_partial_selected_clause_steps[OF selection index clause ordinary failed,
      where es=saved] initial by auto
  let ?saved = "map (\<lambda>d. LPCClause (LPCAtom ?call#pending) d mark) cs @ LPCBarrier mark#saved"
  have ctx: "lpp_caller_numeric_context H K rho ?env (\<lambda>y. CHR ''1''#y)"
    by (rule lpp_caller_numeric_initial)
  obtain next_eta next_names next_pending bars where typed:
      "lpp_caller_numeric_context H (lpp_helper_prefix_known K ops)
        (lpp_helper_prefix_values ops rho) next_eta next_names"
    and bars: "lp_cut_barriers bars"
    and progressed: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t ?env))
        (map lpp_helper_operation_goal ops @ map (lp_cut_bind mark id) rest) @ ?pending)#?saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t next_eta)) (map (lp_cut_bind mark id) rest) @ next_pending)#(bars@?saved))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    using lpp_checked_helper_prefix_steps[OF checked ctx guards,
      where rest="map (lp_cut_bind mark id) rest" and pending="?pending" and saved="?saved"] by blast
  have prefix: "(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?env))
        (map lpp_helper_operation_goal ops @ rest) @ ?pending)#?saved,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t next_eta)) rest @ next_pending)#(bars@?saved))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    using progressed by (simp only: map_append map_map lp_cut_map_bind lpp_helper_bind_goal o_def id_apply)
  show ?thesis
    apply (rule exI[of _ mark], rule exI[of _ next_eta], rule exI[of _ next_names], rule exI[of _ next_pending], rule exI[of _ bars])
    using typed bars trancl_rtrancl_trancl[OF selected prefix] by (simp only: append_assoc; blast)
qed

ML \<open>
val checked = [@{thm lpp_helper_selected_clause_failure}, @{thm lpp_helper_selected_clause_iteration}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper clause selection" else ();
\<close>
end
