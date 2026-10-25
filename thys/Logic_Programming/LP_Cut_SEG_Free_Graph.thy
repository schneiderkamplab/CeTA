theory LP_Cut_SEG_Free_Graph
  imports LP_Cut_SEG_Free_Region_Check LP_Cut_SEG_Free_Split_Check
begin

datatype 'f lpc_seg_free_component =
  LPCSEGFreeRegion "'f lpc_seg_region" "string list list" | LPCSEGFreeSplit "'f lpc_seg_split"

fun lpc_seg_free_check_component where
  "lpc_seg_free_check_component fuel P roots Fs entry_root F is_cont c d C R (LPCSEGFreeRegion region Ls) =
    lpc_seg_free_check_region fuel P roots Fs entry_root F is_cont c d C R region Ls"
| "lpc_seg_free_check_component fuel P roots Fs entry_root F is_cont c d C R (LPCSEGFreeSplit receipt) =
    lpc_seg_free_check_split fuel P roots Fs entry_root F is_cont c d C R receipt"

theorem lpc_seg_free_component_checked_lower:
  assumes checked: "lpc_seg_free_check_component fuel P roots Fs entry_root F is_cont c d C R component"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node entry_root)))
      (lpcn_guards (lpcsr_node entry_root)) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input entry_root) eta)"
    and lower: "\<And>us v out. (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input entry_root) eta\<rangle>,v)
      \<in>(qrstep False Q R)\<^sup>+ \<Longrightarrow> lpc_seg_free_root_rep roots Fs is_cont c d us v out \<Longrightarrow>
      lpc_return_contract P us (qrstep False Q R) v out"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root)) (qrstep False Q R)
    (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input entry_root) eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output entry_root) rho\<rangle>)"
proof (cases component)
  case (LPCSEGFreeRegion region Ls)
  show ?thesis by (rule lpc_seg_free_region_checked_lower[OF _ program known free finite lower range roots])
    (use checked in \<open>simp add: LPCSEGFreeRegion\<close>)
next
  case (LPCSEGFreeSplit receipt)
  show ?thesis by (rule lpc_seg_free_split_checked_lower[OF _ program known free finite lower range roots])
    (use checked in \<open>simp add: LPCSEGFreeSplit\<close>)
qed


definition lpc_seg_free_check_graph where
  "lpc_seg_free_check_graph fuel P roots Fs regions q modes is_cont c d C R =
    (lp_cut_source_program P \<and> roots\<noteq>[] \<and> length roots=length Fs \<and> Fs!0=[] \<and> length roots=length regions \<and>
      (let nd=lpcsr_node (roots!0) in
        lp_cut_check_root q modes (lpcn_vars nd) (lpcn_state nd) (lpcn_ground nd) (lpcn_guards nd) \<and>
        vars_term (lpcsr_input (roots!0)) \<subseteq> set (lpcn_ground nd)) \<and>
      list_all (\<lambda>i. lpc_seg_free_check_component fuel P roots Fs (roots!i) (Fs!i) is_cont c d C R (regions!i))
        [0..<length roots])"

theorem lpc_seg_free_graph_contract:
  assumes checked: "lpc_seg_free_check_graph fuel P roots Fs regions q modes is_cont c d C R"
    and sn: "SN (qrstep False N R)"
    and rep: "lpc_seg_free_root_rep roots Fs is_cont c d ss t ret"
    and range: "range d \<subseteq> C"
    and normal_roots: "\<And>q. q\<in>N \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "lpc_return_contract P ss (qrstep False N R) t ret"
proof (rule lpc_return_contract_modular[where rep="lpc_seg_free_root_rep roots Fs is_cont c d",
    OF SN_on_subset2[OF subset_UNIV sn] rep])
  fix us u out
  assume represented: "lpc_seg_free_root_rep roots Fs is_cont c d us u out"
    and lower: "\<And>vs v f. (u,v)\<in>(qrstep False N R)\<^sup>+ \<Longrightarrow>
      lpc_seg_free_root_rep roots Fs is_cont c d vs v f \<Longrightarrow> lpc_return_contract P vs (qrstep False N R) v f"
  obtain i eta A where index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node (roots!i))))
      (lpcn_guards (lpcsr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input (roots!i)) eta)"
    and source: "us=lpc_return_eval eta (lpc_seg_root_state (roots!i))"
    and measure: "u=A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>"
    and returns: "out=(\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output (roots!i)) rho\<rangle>)"
    using represented by (auto simp: lpc_seg_free_root_rep_def)
  have local: "lpc_seg_free_check_component fuel P roots Fs (roots!i) (Fs!i) is_cont c d C R (regions!i)"
    and program: "lp_cut_source_program P"
    using checked index by (auto simp: lpc_seg_free_check_graph_def list_all_iff)
  have lower': "lpc_return_contract P vs (qrstep False N R) v f"
    if strict: "(A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input (roots!i)) eta\<rangle>,v)\<in>(qrstep False N R)\<^sup>+"
    and rep: "lpc_seg_free_root_rep roots Fs is_cont c d vs v f" for vs v f
    by (rule lower[OF _ rep]) (use strict in \<open>simp only: measure\<close>)
  show "lpc_return_contract P us (qrstep False N R) u out"
    unfolding source measure returns
    by (rule lpc_seg_free_component_checked_lower[OF local program known free finite lower' range normal_roots])
qed

theorem lpc_seg_free_graph_root_sound:
  fixes ts :: "('f lp_cut_symbol,string) lp_iterm list"
  assumes checked: "lpc_seg_free_check_graph fuel P roots Fs regions q modes is_cont c d C R"
    and sn: "SN (qrstep False N R)"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
    and range: "range d \<subseteq> C"
    and normal_roots: "\<And>q. q\<in>N \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "SN_on (lp_cut_mgu_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  let ?entry = "roots!0"
  let ?nd = "lpcsr_node ?entry"
  let ?vs = "lpcn_vars ?nd"
  let ?eta = "lp_cut_query_env ?vs ts"
  have nonempty: "roots\<noteq>[]"
    and root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and vars: "vars_term (lpcsr_input ?entry) \<subseteq> set (lpcn_ground ?nd)"
    using checked by (auto simp: lpc_seg_free_check_graph_def Let_def)
  have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_values: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    using root finite_values by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have finite: "lp_seg_ground (lp_ieval (lpcsr_input ?entry) ?eta)"
    using known vars by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
  have index: "0<length roots" using nonempty by simp
  have free: "lpc_free_knowledge (set (Fs!0)) ?eta"
    using checked by (simp add: lpc_seg_free_check_graph_def lpc_free_knowledge_def)
  have represented: "lpc_seg_free_root_rep roots Fs is_cont c d
      (lpc_return_eval ?eta (lpc_seg_root_state ?entry))
      (\<box>\<langle>lpc_seg_return_value is_cont c d (lpcsr_input ?entry) ?eta\<rangle>)
      (\<lambda>rho. \<box>\<langle>lpc_seg_return_value is_cont c d (lpcsr_output ?entry) rho\<rangle>)"
    by (rule lpc_seg_free_root_repI[OF index known free finite])
  have contract: "lpc_return_contract P (lpc_return_eval ?eta (lpc_seg_root_state ?entry)) (qrstep False N R)
      (\<box>\<langle>lpc_seg_return_value is_cont c d (lpcsr_input ?entry) ?eta\<rangle>)
      (\<lambda>rho. \<box>\<langle>lpc_seg_return_value is_cont c d (lpcsr_output ?entry) rho\<rangle>)"
    by (rule lpc_seg_free_graph_contract[OF checked sn represented range normal_roots])
  have source: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using contract by (simp add: lpc_return_contract_def lpc_return_eval_erases lpc_seg_root_state_def map_map o_def)
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed

end
