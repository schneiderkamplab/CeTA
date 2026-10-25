theory LP_Cut_SEG_Certificate
  imports LP_Cut_SEG_Graph LP_TOCL09_Checker
begin

definition check_lpc_seg_certificate where
  "check_lpc_seg_certificate I J fuel P roots regions q modes continuations controls data_map fallback constructors trs_rules prf =
    (list_all (\<lambda>p. snd p\<in>set constructors) data_map \<and>
     fallback\<in>set constructors \<and>
     list_all (\<lambda>(l,r). case l of Var x \<Rightarrow> False | Fun f ts \<Rightarrow> f\<notin>set constructors) trs_rules \<and>
     lpc_seg_check_graph fuel P roots regions q modes
       (\<lambda>f. f\<in>set continuations) (lpc_lookup fallback controls)
       (lpc_lookup fallback data_map) (set constructors) (set trs_rules) \<and>
     isOK (check_trs_termination_proof I J False id
       (tp_ops.mk I False (map fst trs_rules) trs_rules []) prf))"

theorem check_lpc_seg_certificate_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "check_lpc_seg_certificate I J fuel P roots regions q modes continuations controls data_map fallback constructors trs_rules prf"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lp_cut_mgu_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  interpret tp_spec I by (rule I)
  have child: "isOK (check_trs_termination_proof I J False id
       (tp_ops.mk I False (map fst trs_rules) trs_rules []) prf)"
    using checked by (simp add: check_lpc_seg_certificate_def)
  have sn: "SN (qrstep False (fst ` set trs_rules) (set trs_rules))"
    using check_trs_termination_proof[OF I J child] by simp
  have graph: "lpc_seg_check_graph fuel P roots regions q modes
       (\<lambda>f. f\<in>set continuations) (lpc_lookup fallback controls)
       (lpc_lookup fallback data_map) (set constructors) (set trs_rules)"
    using checked by (simp add: check_lpc_seg_certificate_def)
  have range: "range (lpc_lookup fallback data_map) \<subseteq> set constructors"
  proof
    fix y assume "y\<in>range (lpc_lookup fallback data_map)"
    then obtain x where y: "y=lpc_lookup fallback data_map x" by blast
    show "y\<in>set constructors"
    proof (cases "map_of data_map x")
      case None then show ?thesis using checked y
        by (simp add: check_lpc_seg_certificate_def lpc_lookup_def)
    next
      case (Some z)
      have "(x,z)\<in>set data_map" by (rule map_of_SomeD[OF Some])
      then show ?thesis using checked y Some
        by (auto simp: check_lpc_seg_certificate_def lpc_lookup_def list_all_iff)
    qed
  qed
  have normal: "\<exists>g us. t=Fun g us \<and> g\<notin>set constructors"
    if "t\<in>fst ` set trs_rules" for t
    using checked that by (auto simp: check_lpc_seg_certificate_def list_all_iff split: term.splits)
  show ?thesis
    by (rule lpc_seg_graph_root_sound[OF graph sn len ground range normal])
qed

end
