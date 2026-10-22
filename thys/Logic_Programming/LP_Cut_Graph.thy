theory LP_Cut_Graph
  imports LP_Cut_Source LP_Infinite_Resolution
begin

text \<open>Guarded cut-state graphs target ordinary residual LP obligations.
The representation relation includes the complete choice stack and path guards.
Every possible source successor must be covered. Zero-cost edges are allowed
only when the administrative weight decreases; thus a cycle cannot disappear
in residual extraction. This is the semantic theorem; executable local coverage
checking is a separate obligation, not assumed by a production checker.\<close>

definition lp_cut_graph_valid where
  "lp_cut_graph_valid P Q rep =
    (\<forall>s qs. rep s qs \<longrightarrow> (\<forall>t. (s,t)\<in>lp_cut_source P \<longrightarrow>
      ((\<exists>rs. (qs,rs)\<in>(lp_ild Q)\<^sup>+ \<and> rep t rs) \<or>
       (rep t qs \<and> lp_cut_weight t < lp_cut_weight s))))"

theorem lp_cut_graph_residual_termination:
  assumes valid: "lp_cut_graph_valid P Q rep"
    and sn: "SN_on (lp_ild Q) {qs}"
    and represented: "rep s qs"
  shows "SN_on (lp_cut_source P) {s}"
proof -
  have snplus: "SN_on ((lp_ild Q)\<^sup>+) {qs}" by (rule SN_on_trancl[OF sn])
  have all: "\<forall>s. rep s qs \<longrightarrow> SN_on (lp_cut_source P) {s}"
  proof (rule SN_on_induct[OF snplus singletonI])
    fix xs
    assume outer: "\<And>ys. (xs,ys)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      \<forall>t. rep t ys \<longrightarrow> SN_on (lp_cut_source P) {t}"
    have local: "\<And>k. \<forall>s. lp_cut_weight s=k \<longrightarrow> rep s xs \<longrightarrow> SN_on (lp_cut_source P) {s}"
    proof -
      fix k show "\<forall>s. lp_cut_weight s=k \<longrightarrow> rep s xs \<longrightarrow> SN_on (lp_cut_source P) {s}"
      proof (induct k rule: less_induct)
        case (less k)
        show ?case
        proof (intro allI impI)
          fix s assume weight: "lp_cut_weight s=k" and rep: "rep s xs"
          show "SN_on (lp_cut_source P) {s}"
          proof (rule step_reflects_SN_on)
            fix t assume step: "(s,t)\<in>lp_cut_source P"
            have covered: "(\<exists>rs. (xs,rs)\<in>(lp_ild Q)\<^sup>+ \<and> rep t rs) \<or>
              (rep t xs \<and> lp_cut_weight t < lp_cut_weight s)"
              using valid rep step by (auto simp: lp_cut_graph_valid_def)
            show "SN_on (lp_cut_source P) {t}"
              using covered outer less.hyps weight by blast
          qed
        qed
      qed
    qed
    show "\<forall>s. rep s xs \<longrightarrow> SN_on (lp_cut_source P) {s}"
      using local by blast
  qed
  show ?thesis using all represented by blast
qed

end
