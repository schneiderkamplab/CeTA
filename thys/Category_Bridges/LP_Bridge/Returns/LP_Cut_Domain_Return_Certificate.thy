theory LP_Cut_Domain_Return_Certificate
  imports LP_Cut_Domain_Return_Check
begin

context cut_runtime_domain
begin

theorem precise_return_root_sound:
  fixes ts :: "('f lp_cut_symbol,string) term list"
    and p d :: "'f lp_cut_symbol\<Rightarrow>'b"
  assumes checked: "lpc_return_check_root fuel P Q nds states returned arity acts r q modes"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)) \<Longrightarrow>
      SN_on (lp_ild (lp_roles_program p d Q))
        {[(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  let ?nd = "nds!r"
  let ?vs = "lpcn_vars ?nd"
  let ?vals = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  let ?env = "lp_cut_query_env ?vs ?vals"
  have root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and table: "lpc_check_return_table fuel P Q nds states returned arity acts" and bound: "r<length nds"
    and program: "lp_cut_source_program P"
    using checked by (auto simp: lpc_return_check_root_def)
  have lengths: "length ?vs=length ?vals" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?env ?vs=?vals" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_index: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> lp_seg_ground (?vals!i)"
    using ground len by (auto simp: lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  have finite: "\<forall>(t,b)\<in>set (zip ?vals modes). b \<longrightarrow> lp_seg_ground t"
    using finite_index len by (auto simp: in_set_zip)
  have finite': "\<forall>(t,b)\<in>set (zip (map ?env ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using finite by (simp only: vals)
  have envD: "\<forall>x. D (?env x)"
    by (intro allI; rule query_env_domain) (auto intro: valuation_domain variables)
  have known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?env"
    using root finite' envD by (auto simp: lp_cut_check_root_def knowledge_def zip_map1)
  have mapped: "SN_on (lp_ild (lp_roles_program p d Q))
    {[(p (lpcn_pred ?nd),map (\<lambda>t. lp_ieval t LPIVar) (map (map_term d id) ts))]}"
    by (rule child) (use len ground in \<open>auto simp: lpc_positions_def\<close>)
  have residual: "SN_on (lp_ild Q) {[(lpcn_pred ?nd,map ?env ?vs)]}"
    by (rule lp_roles_termination_reflect[where p=p and d=d])
      (use mapped vals in \<open>simp add: lp_roles_iatom_def map_map o_def lp_map_finite_eval\<close>)
  have contract: "precise_return_contract P (lpc_return_eval ?env (states!r)) (lp_ild Q)
    [(lpcn_pred ?nd,map ?env ?vs)] (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule precise_return_table_contract[OF table program bound known residual])
  have state: "map fst (states!r)=lpcn_state ?nd"
    using table bound by (auto simp: lpc_check_return_table_def list_all_iff)
  have source: "SN_on (precise_source P) {lp_cut_state_eval (lpcn_state ?nd) ?env}"
    using contract by (simp add: precise_return_contract_def lpc_return_eval_erases state)
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed

end

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem precise_return_constructor_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpc_return_constructor I J fuel P Q nds states returned arity acts r q modes predicates constructors
      R outs fallback names marks filters q' n positions seed nfs prf"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule precise_return_root_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ len ground])
  show "lpc_return_check_root fuel P Q nds states returned arity acts r q modes"
    using ok by (simp add: check_lpc_return_constructor_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_constructor I J R outs fallback names marks filters q' n positions seed nfs prf"
    using ok by (auto simp: check_lpc_return_constructor_def Let_def)
  have "SN_on (lp_ild R) {[(q',map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule check_lp_constructor_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpc_return_constructor_def Let_def\<close>)
  then show "SN_on (lp_ild (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
    {[(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    using ok by (auto simp: check_lpc_return_constructor_def Let_def)
qed


end
end
