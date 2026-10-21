theory LP_SEG_Certificate
  imports LP_SEG_Check LP_TOCL09_Checker
begin

definition check_lp_seg where
  "check_lp_seg I J fuel P nds trs_rules root_id q n positions prf =
    (lp_check_seg_graph fuel P nds trs_rules root_id \<and>
     lp_seg_node_goals nds root_id=[(q,map Var (lp_source_query_args n))] \<and>
     lp_seg_node_ground nds root_id=map (\<lambda>i. lp_source_query_args n ! i) positions \<and>
     list_all (\<lambda>i. i<n) positions \<and>
     isOK (check_trs_termination_proof I J False id
       (tp_ops.mk I False [] trs_rules []) prf))"

theorem check_lp_seg_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) lp_iterm list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "check_lp_seg I J fuel P nds trs_rules root_id q n positions prf"
    and len: "length ts=n"
    and ground: "\<forall>i\<in>set positions. lp_seg_ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,ts)]}"
proof -
  interpret tp_spec I by (rule I)
  have child: "isOK (check_trs_termination_proof I J False id
    (tp_ops.mk I False [] trs_rules []) prf)"
    using checked by (simp add: check_lp_seg_def)
  have sn: "SN (rstep (set trs_rules))"
    using check_trs_termination_proof[OF I J child]
    by (simp add: SN_qrel_def)
  show ?thesis by (rule lp_seg_query_sound[OF _ sn _ _ _ len ground])
    (use checked in \<open>auto simp: check_lp_seg_def list_all_iff\<close>)
qed

end
