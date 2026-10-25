theory LP_Cut_SEG_Projected_Relation
  imports LP_Cut_SEG_Projected_Emit LP_Cut_Return_Modular
begin

hide_const (open) CPF_Proof_Parser.rstep

text \<open>Keep runtime observations in the return contract. A recursive
return obtains a finite filtered value from reachability, rather than a
separate and unnecessarily strong groundness premise. Pending continuations
remain part of the induction measure.\<close>

definition lpc_seg_projected_rel ::
  "'f afs \<Rightarrow> ('f,string) trs \<Rightarrow> ('f,string) lp_iterm rel" where
  "lpc_seg_projected_rel filtering R = {(s,t). \<exists>m n.
    lp_iproject filtering s m \<and> lp_iproject filtering t n \<and>
    (m,n)\<in>rstep (af_rule filtering ` R)}"

definition lpc_seg_has_projection :: "'f afs \<Rightarrow> ('f,string) lp_iterm \<Rightarrow> bool" where
  "lpc_seg_has_projection filtering s = (\<exists>m::('f,string) term. lp_iproject filtering s m)"

lemma lpc_seg_projected_reachable:
  assumes path: "(s,t)\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
    and observed: "lpc_seg_has_projection filtering s"
  shows "lpc_seg_has_projection filtering t"
  using path observed
  by (induct rule: rtrancl_induct)
    (auto simp: lpc_seg_projected_rel_def lpc_seg_has_projection_def)

theorem lpc_seg_projected_SN:
  fixes filtering :: "'f afs"
  assumes sn: "SN_on (rstep (af_rule filtering ` R)) {m}"
    and initial: "lp_iproject filtering s m"
  shows "SN_on (lpc_seg_projected_rel filtering R) {s}"
proof -
  have all: "\<forall>s. lp_iproject filtering s m \<longrightarrow> SN_on (lpc_seg_projected_rel filtering R) {s}"
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix m and s :: "('f,string) lp_iterm"
    assume ih: "\<And>n. (m,n)\<in>rstep (af_rule filtering ` R) \<Longrightarrow>
      \<forall>t. lp_iproject filtering t n \<longrightarrow> SN_on (lpc_seg_projected_rel filtering R) {t}"
      and pr: "lp_iproject filtering s m"
    show "SN_on (lpc_seg_projected_rel filtering R) {s}"
    proof (rule step_reflects_SN_on)
      fix t assume edge: "(s,t)\<in>lpc_seg_projected_rel filtering R"
      obtain a b where left: "lp_iproject filtering s a" and right: "lp_iproject filtering t b"
        and step: "(a,b)\<in>rstep (af_rule filtering ` R)"
        using edge by (auto simp: lpc_seg_projected_rel_def)
      have equal: "a=m" by (rule lp_iproject_unique[OF left pr])
      show "SN_on (lpc_seg_projected_rel filtering R) {t}" using ih step right equal by auto
    qed
  qed
  show ?thesis using all initial by auto
qed

lemma lpc_seg_projected_emit_edge:
  fixes filtering :: "'g afs"
  assumes checked: "lpc_seg_check_projected_pair filtering nl nr is_cont c d R l r"
    and observed: "lpc_seg_has_projection filtering
      (lpc_seg_role_value nl is_cont c d (lp_ieval l eta))"
  shows "(lpc_seg_role_value nl is_cont c d (lp_ieval l eta),
    lpc_seg_role_value nr is_cont c d (lp_ieval r eta))\<in>lpc_seg_projected_rel filtering R"
proof -
  obtain m :: "('g,string) term" where pr: "lp_iproject filtering
    (lpc_seg_role_value nl is_cont c d (lp_ieval l eta)) m"
    using observed by (auto simp: lpc_seg_has_projection_def)
  obtain n where target: "lp_iproject filtering
      (lpc_seg_role_value nr is_cont c d (lp_ieval r eta)) n"
    and step: "(m,n)\<in>rstep (af_rule filtering ` R)"
    by (rule lpc_seg_checked_projected_pair[OF checked pr]) blast
  show ?thesis using pr target step by (auto simp: lpc_seg_projected_rel_def)
qed

theorem lpc_seg_projected_recursive_split:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and lower: "\<And>vs v out. (t,v)\<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      rep vs v out \<Longrightarrow> lpc_return_contract P vs (lpc_seg_projected_rel filtering R) v out"
    and entry: "(t,p)\<in>(lpc_seg_projected_rel filtering R)\<^sup>+"
    and prefix_rep: "rep ss p ret"
    and initial: "lpc_seg_has_projection filtering p"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. (p,ret eta)\<in>(lpc_seg_projected_rel filtering R)\<^sup>* \<Longrightarrow>
      lpc_seg_has_projection filtering (ret eta) \<Longrightarrow> \<exists>v.
      (ret eta,v)\<in>(lpc_seg_projected_rel filtering R)\<^sup>* \<and>
      rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] v final"
  shows "lpc_return_contract P (lpc_attach_answers rest ss) (lpc_seg_projected_rel filtering R) t final"
proof (rule lpc_return_split_lower[where rep=rep and R="lpc_seg_projected_rel filtering R"
    and t=t and p=p and ss=ss and ret=ret and final=final and rest=rest,
    OF program lower entry prefix_rep valid separated])
  fix eta assume reached: "(p,ret eta)\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
  have observed: "lpc_seg_has_projection filtering (ret eta)"
    by (rule lpc_seg_projected_reachable[OF reached initial])
  show "\<exists>v. (ret eta,v)\<in>(lpc_seg_projected_rel filtering R)\<^sup>* \<and>
    rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] v final"
    by (rule continuation[OF reached observed])
qed

lemma lpc_seg_projected_contract_answer:
  assumes contract: "lpc_return_contract P ss (lpc_seg_projected_rel filtering R) t ret"
    and initial: "lpc_seg_has_projection filtering t"
    and actual: "lpc_actual_return P ss eta"
  shows "lpc_seg_has_projection filtering (ret eta)"
proof -
  have reached: "(t,ret eta)\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
    using contract actual by (auto simp: lpc_return_contract_def lpc_actual_return_def)
  show ?thesis by (rule lpc_seg_projected_reachable[OF reached initial])
qed

end
