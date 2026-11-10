theory LP_Cut_Domain_SEG_Graph
 imports LP_Cut_Domain_SEG_Split_Check
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_component_checked_lower:
  assumes checked: "lpc_seg_check_component fuel P roots entry_root is_cont c d C R component"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground (lpcsr_node entry_root)))
      (lpcn_guards (lpcsr_node entry_root)) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input entry_root) eta)"
    and lower: "\<And>us v out. (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input entry_root) eta\<rangle>,v)
      \<in>(qrstep False Q R)\<^sup>+ \<Longrightarrow> precise_seg_root_rep roots is_cont c d us v out \<Longrightarrow>
      precise_return_contract P us (qrstep False Q R) v out"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "precise_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root)) (qrstep False Q R)
    (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input entry_root) eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output entry_root) rho\<rangle>)"
proof (cases component)
  case (LPCSEGRegion region)
  show ?thesis by (rule precise_seg_region_checked_lower[OF _ program known finite lower range roots])
    (use checked in \<open>simp add: LPCSEGRegion\<close>)
next
  case (LPCSEGSplit receipt)
  show ?thesis by (rule precise_seg_split_checked_lower[OF _ program known finite lower range roots])
    (use checked in \<open>simp add: LPCSEGSplit\<close>)
qed



theorem precise_seg_graph_contract:
  assumes checked: "lpc_seg_check_graph fuel P roots regions q modes is_cont c d C R"
    and sn: "SN (qrstep False N R)"
    and rep: "precise_seg_root_rep roots is_cont c d ss t ret"
    and range: "range d \<subseteq> C"
    and normal_roots: "\<And>q. q\<in>N \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "precise_return_contract P ss (qrstep False N R) t ret"
proof (rule precise_return_contract_modular[where rep="precise_seg_root_rep roots is_cont c d",
    OF SN_on_subset2[OF subset_UNIV sn] rep])
  fix us u out
  assume represented: "precise_seg_root_rep roots is_cont c d us u out"
    and lower: "\<And>vs v f. (u,v)\<in>(qrstep False N R)\<^sup>+ \<Longrightarrow>
      precise_seg_root_rep roots is_cont c d vs v f \<Longrightarrow> precise_return_contract P vs (qrstep False N R) v f"
  obtain i eta A where index: "i<length roots"
    and known: "knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
      (lpcn_guards (lpcsr_node (roots!i))) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input (roots!i)) eta)"
    and source: "us=lpc_return_eval eta (lpc_seg_root_state (roots!i))"
    and measure: "u=A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>"
    and returns: "out=(\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output (roots!i)) rho\<rangle>)"
    using represented by (auto simp: precise_seg_root_rep_def)
  have local: "lpc_seg_check_component fuel P roots (roots!i) is_cont c d C R (regions!i)"
    and program: "lp_cut_source_program P"
    using checked index by (auto simp: lpc_seg_check_graph_def list_all_iff)
  have lower': "precise_return_contract P vs (qrstep False N R) v f"
    if strict: "(A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>,v)\<in>(qrstep False N R)\<^sup>+"
    and rep: "precise_seg_root_rep roots is_cont c d vs v f" for vs v f
    by (rule lower[OF _ rep]) (use strict in \<open>simp only: measure\<close>)
  show "precise_return_contract P us (qrstep False N R) u out"
    unfolding source measure returns
    by (rule precise_seg_component_checked_lower[OF local program known finite lower' range normal_roots])
qed


theorem precise_seg_graph_root_sound:
  fixes ts :: "('f lp_cut_symbol,string) lp_iterm list"
  assumes checked: "lpc_seg_check_graph fuel P roots regions q modes is_cont c d C R"
    and sn: "SN (qrstep False N R)"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
    and domains: "list_all D ts"
    and range: "range d \<subseteq> C"
    and normal_roots: "\<And>q. q\<in>N \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "SN_on (precise_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  let ?entry = "roots!0"
  let ?nd = "lpcsr_node ?entry"
  let ?vs = "lpcn_vars ?nd"
  let ?eta = "lp_cut_query_env ?vs ts"
  have nonempty: "roots\<noteq>[]"
    and root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and vars: "vars_term (lpcsr_input ?entry) \<subseteq> set (lpcn_ground ?nd)"
    using checked by (auto simp: lpc_seg_check_graph_def Let_def)
  have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_values: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have envD: "\<forall>x. D (?eta x)"
    by (intro allI; rule query_env_domain) (use domains in \<open>auto simp: list_all_iff\<close>)
  have known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    using root finite_values envD by (auto simp: lp_cut_check_root_def knowledge_def zip_map1)
  have finite: "lp_seg_ground (lp_ieval (lpcsr_input ?entry) ?eta)"
    using known vars by (auto simp: knowledge_def lp_seg_ground_eval)
  have index: "0<length roots" using nonempty by simp
  have represented: "precise_seg_root_rep roots is_cont c d
      (lpc_return_eval ?eta (lpc_seg_root_state ?entry))
      (\<box>\<langle>lpc_seg_return_value is_cont c d (lpcsr_input ?entry) ?eta\<rangle>)
      (\<lambda>rho. \<box>\<langle>lpc_seg_return_value is_cont c d (lpcsr_output ?entry) rho\<rangle>)"
    by (rule precise_seg_root_repI[OF index known finite])
  have contract: "precise_return_contract P (lpc_return_eval ?eta (lpc_seg_root_state ?entry)) (qrstep False N R)
      (\<box>\<langle>lpc_seg_return_value is_cont c d (lpcsr_input ?entry) ?eta\<rangle>)
      (\<lambda>rho. \<box>\<langle>lpc_seg_return_value is_cont c d (lpcsr_output ?entry) rho\<rangle>)"
    by (rule precise_seg_graph_contract[OF checked sn represented range normal_roots])
  have source: "SN_on (precise_source P) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using contract by (simp add: precise_return_contract_def lpc_return_eval_erases lpc_seg_root_state_def map_map o_def)
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed


end
end
