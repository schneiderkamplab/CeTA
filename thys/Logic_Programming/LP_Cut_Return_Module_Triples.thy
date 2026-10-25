theory LP_Cut_Return_Module_Triples
  imports LP_Cut_Return_Module_Certificate LP_Dependency_Triple_Checker
begin

definition check_lpc_return_module_triples where
  "check_lpc_return_module_triples I J fuel P Q nds states returned arity acts r q modes predicates constructors
      D R outs fallback dnames pnames marks filters q' n positions labs proofs =
    (lpc_return_module_check_root fuel P Q nds states returned arity acts r q modes \<and>
     (let p=lpc_lookup fallback predicates; d=lpc_lookup fallback constructors in
       R = lp_roles_program p d Q \<and> q' = p (lpcn_pred (nds!r)) \<and>
       n=length modes \<and> positions=lpc_positions modes \<and>
       check_lp_initial_triples I J D R outs fallback dnames pnames marks filters q' n positions labs proofs))"

theorem check_lpc_return_module_triples_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpc_return_module_triples I J fuel P Q nds states returned arity acts r q modes predicates constructors
      D R outs fallback dnames pnames marks filters q' n positions labs proofs"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpc_return_module_root_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ len ground])
  show "lpc_return_module_check_root fuel P Q nds states returned arity acts r q modes"
    using ok by (simp add: check_lpc_return_module_triples_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_initial_triples I J D R outs fallback dnames pnames marks filters q' n positions labs proofs"
    using ok by (auto simp: check_lpc_return_module_triples_def Let_def)
  have "SN_on (lp_ild R) {[(q',map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule check_lp_initial_triples_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpc_return_module_triples_def Let_def\<close>)
  then show "SN_on (lp_ild (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
    {[(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    using ok by (auto simp: check_lpc_return_module_triples_def Let_def)
qed


end
