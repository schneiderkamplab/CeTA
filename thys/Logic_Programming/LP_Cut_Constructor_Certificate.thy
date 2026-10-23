theory LP_Cut_Constructor_Certificate
  imports LP_Cut_Table_Certificate LP_Cut_MGU_Normalize
begin

definition check_lpc_constructor where
  "check_lpc_constructor I J fuel P Q nds acts r q modes predicates constructors
      R outs fallback names marks filters q' n positions seed nfs prf =
    (lpc_check_root_table fuel P Q nds acts r q modes \<and>
     (let p=lpc_lookup fallback predicates; d=lpc_lookup fallback constructors in
       R = lp_roles_program p d Q \<and> q' = p (lpcn_pred (nds!r)) \<and>
       n=length modes \<and> positions=lpc_positions modes \<and>
       check_lp_constructor I J R outs fallback names marks filters q' n positions seed nfs prf))"

theorem check_lpc_constructor_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpc_constructor I J fuel P Q nds acts r q modes predicates constructors
      R outs fallback names marks filters q' n positions seed nfs prf"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpc_root_table_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ len ground])
  show "lpc_check_root_table fuel P Q nds acts r q modes"
    using ok by (simp add: check_lpc_constructor_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_constructor I J R outs fallback names marks filters q' n positions seed nfs prf"
    using ok by (auto simp: check_lpc_constructor_def Let_def)
  have "SN_on (lp_ild R) {[(q',map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule check_lp_constructor_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpc_constructor_def Let_def\<close>)
  then show "SN_on (lp_ild (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
    {[(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    using ok by (auto simp: check_lpc_constructor_def Let_def)
qed

corollary check_lpc_constructor_mgu_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes "tp_spec I" "dpp_spec J"
    "check_lpc_constructor I J fuel P Q nds acts r q modes predicates constructors
      R outs fallback names marks filters q' n positions seed nfs prf"
    "length ts=length modes"
    "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule lp_cut_conservative_implies_mgu_SN,
      rule check_lpc_constructor_sound[OF assms])

end
