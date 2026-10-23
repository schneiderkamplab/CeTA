theory LP_Cut_Table_Certificate
  imports LP_Cut_Table_Check LP_Residual_Roles LP_Constructor_XML
begin

definition lpc_positions where
  "lpc_positions modes = filter (\<lambda>i. modes!i) [0..<length modes]"

definition lpc_check_root_table where
  "lpc_check_root_table fuel P Q nds acts r q modes =
    (r<length nds \<and> lpc_check_table fuel P Q nds acts \<and>
     lp_cut_check_root q modes (lpcn_vars (nds!r)) (lpcn_state (nds!r))
       (lpcn_ground (nds!r)) (lpcn_guards (nds!r)))"

theorem lpc_root_table_sound:
  fixes ts :: "('a lp_cut_symbol,string) term list"
    and p d :: "'a lp_cut_symbol\<Rightarrow>'b"
  assumes checked: "lpc_check_root_table fuel P Q nds acts r q modes"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)) \<Longrightarrow>
      SN_on (lp_ild (lp_roles_program p d Q))
        {[(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
  shows "SN_on (lp_cut_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  let ?nd = "nds!r"
  let ?vs = "lpcn_vars ?nd"
  let ?vals = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  let ?env = "lp_cut_query_env ?vs ?vals"
  have root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and table: "lpc_check_table fuel P Q nds acts" and bound: "r<length nds"
    using checked by (auto simp: lpc_check_root_table_def)
  have lengths: "length ?vs=length ?vals" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?env ?vs=?vals" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_index: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> lp_seg_ground (?vals!i)"
    using ground len by (auto simp: lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  have finite: "\<forall>(t,b)\<in>set (zip ?vals modes). b \<longrightarrow> lp_seg_ground t"
    using finite_index len by (auto simp: in_set_zip)
  have finite': "\<forall>(t,b)\<in>set (zip (map ?env ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using finite by (simp only: vals)
  have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?env"
    using root finite' by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have mapped: "SN_on (lp_ild (lp_roles_program p d Q))
    {[(p (lpcn_pred ?nd),map (\<lambda>t. lp_ieval t LPIVar) (map (map_term d id) ts))]}"
    by (rule child) (use len ground in \<open>auto simp: lpc_positions_def\<close>)
  have residual: "SN_on (lp_ild Q) {[(lpcn_pred ?nd,map ?env ?vs)]}"
    by (rule lp_roles_termination_reflect[where p=p and d=d])
      (use mapped vals in \<open>simp add: lp_roles_iatom_def map_map o_def lp_map_finite_eval\<close>)
  have source: "SN_on (lp_cut_source P) {lp_cut_state_eval (lpcn_state ?nd) ?env}"
    by (rule lpc_table_sound[OF table bound known residual])
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed

definition lpc_lookup where
  "lpc_lookup fallback entries x = the_default fallback (map_of entries x)"

definition check_lpc_tocl where
  "check_lpc_tocl I J fuel P Q nds acts r q modes predicates constructors
      R outs fallback names filters q' n positions prf =
    (lpc_check_root_table fuel P Q nds acts r q modes \<and>
     (let p=lpc_lookup fallback predicates; d=lpc_lookup fallback constructors in
       R = lp_roles_program p d Q \<and> q' = p (lpcn_pred (nds!r)) \<and>
       n=length modes \<and> positions=lpc_positions modes \<and>
       check_lp_finite I J R outs fallback names filters q' n positions prf))"

theorem check_lpc_tocl_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpc_tocl I J fuel P Q nds acts r q modes predicates constructors
      R outs fallback names filters q' n positions prf"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpc_root_table_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ len ground])
  show "lpc_check_root_table fuel P Q nds acts r q modes"
    using ok by (simp add: check_lpc_tocl_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_finite I J R outs fallback names filters q' n positions prf"
    using ok by (auto simp: check_lpc_tocl_def Let_def)
  have "SN_on (lp_ild R) {[(q',map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule check_lp_tocl09_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpc_tocl_def Let_def\<close>)
  then show "SN_on (lp_ild (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
    {[(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    using ok by (auto simp: check_lpc_tocl_def Let_def)
qed

end
