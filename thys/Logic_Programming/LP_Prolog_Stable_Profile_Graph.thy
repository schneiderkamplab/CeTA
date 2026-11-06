theory LP_Prolog_Stable_Profile_Graph
  imports LP_Prolog_Stable_Profile_Operations LP_Prolog_Stable_Numeric_Graph
begin

text \<open>The checked graph is valid for every fixed interpretation outside
its exact integer fragment. In particular the certificate cannot select
floating operation results. Source implementation correspondence and coverage
of source domains remain separate obligations.\<close>

theorem lpp_check_profile_guarded_numeric_graph_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
  assumes checked: "lpp_check_stable_guarded_numeric_graph fuel P D Q T SP transfers roots contexts blocks q modes chain_pred
      OD descents positions coordinates coordinate_modes locations system row_receipts child"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin (lpp_stable_profile_operation fallback)) lpp_finite_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
  by (rule lpp_check_stable_guarded_numeric_graph_sound[
    OF lpp_stable_profile_integer_compatible checked len ground])

ML \<open>
val checked = [@{thm lpp_check_profile_guarded_numeric_graph_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted fixed profile graph dependency" else ();
\<close>
end
