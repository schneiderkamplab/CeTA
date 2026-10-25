theory LP_Cut_Projected_Relation
  imports LP_Cut_Projected_Residual LP_Cut_Return_Modular
begin

hide_const (open) CPF_Proof_Parser.rstep

definition lpc_observes :: "'f afs \<Rightarrow> ('f,string) lp_iatom list \<Rightarrow> ('f,string) term \<Rightarrow> bool" where
  "lpc_observes filtering qs m =
    (\<exists>f ts. qs=[(f,ts)] \<and> lp_iproject filtering (LPIFun f ts) m)"

definition lpc_observed :: "'f afs \<Rightarrow> ('f,string) lp_iatom list \<Rightarrow> bool" where
  "lpc_observed filtering qs = (\<exists>m. lpc_observes filtering qs m)"

definition lpc_projected_rel :: "'f afs \<Rightarrow> ('f,string) trs \<Rightarrow> ('f,string) lp_iatom list rel" where
  "lpc_projected_rel filtering R = {(qs,rs). \<exists>m n.
    lpc_observes filtering qs m \<and> lpc_observes filtering rs n \<and>
    (m,n)\<in>rstep (af_rule filtering ` R)}"

lemma lpc_observes_unique:
  "lpc_observes filtering qs m \<Longrightarrow> lpc_observes filtering qs n \<Longrightarrow> m=n"
  unfolding lpc_observes_def by (auto intro: lp_iproject_unique)

lemma lpc_projected_rel_observed:
  "(qs,rs)\<in>lpc_projected_rel filtering R \<Longrightarrow>
    lpc_observed filtering qs \<and> lpc_observed filtering rs"
  by (auto simp: lpc_projected_rel_def lpc_observed_def)

lemma lpc_projected_reachable_observed:
  assumes path: "(qs,rs)\<in>(lpc_projected_rel filtering R)\<^sup>*"
    and initial: "lpc_observed filtering qs"
  shows "lpc_observed filtering rs"
  using path initial
  by (induct rule: rtrancl_induct) (auto dest: lpc_projected_rel_observed)

theorem lpc_projected_rel_SN:
  assumes sn: "SN_on (rstep (af_rule filtering ` R)) {m}"
    and initial: "lpc_observes filtering qs m"
  shows "SN_on (lpc_projected_rel filtering R) {qs}"
proof -
  have all: "\<forall>qs. lpc_observes filtering qs m \<longrightarrow>
    SN_on (lpc_projected_rel filtering R) {qs}"
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix m qs
    assume ih: "\<And>n. (m,n)\<in>rstep (af_rule filtering ` R) \<Longrightarrow>
      \<forall>rs. lpc_observes filtering rs n \<longrightarrow> SN_on (lpc_projected_rel filtering R) {rs}"
      and observed: "lpc_observes filtering qs m"
    show "SN_on (lpc_projected_rel filtering R) {qs}"
    proof (rule step_reflects_SN_on)
      fix rs assume edge: "(qs,rs)\<in>lpc_projected_rel filtering R"
      obtain a b where left: "lpc_observes filtering qs a"
        and right: "lpc_observes filtering rs b"
        and progress: "(a,b)\<in>rstep (af_rule filtering ` R)"
        using edge by (auto simp: lpc_projected_rel_def)
      have eq: "a=m" by (rule lpc_observes_unique[OF left observed])
      have progress': "(m,b)\<in>rstep (af_rule filtering ` R)" using progress eq by simp
      show "SN_on (lpc_projected_rel filtering R) {rs}" using ih[OF progress'] right by simp
    qed
  qed
  show ?thesis using all initial by simp
qed

text \<open>Recursive Split uses the existing source-bound contract over this
relation. In particular, a prefix return can only enable a continuation if its
projection is finite: this follows from reachability, not from assuming that
all output variables are ground.\<close>

lemma lpc_projected_split_lower:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and lower: "\<And>vs v out. (t,v)\<in>(lpc_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      rep vs v out \<Longrightarrow> lpc_return_contract P vs (lpc_projected_rel filtering R) v out"
    and entry: "(t,p)\<in>(lpc_projected_rel filtering R)\<^sup>+"
    and prefix_rep: "rep ss p ret"
    and initial: "lpc_observed filtering p"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. (p,ret eta)\<in>(lpc_projected_rel filtering R)\<^sup>* \<Longrightarrow>
      lpc_observed filtering (ret eta) \<Longrightarrow> \<exists>v.
      (ret eta,v)\<in>(lpc_projected_rel filtering R)\<^sup>* \<and>
      rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] v final"
  shows "lpc_return_contract P (lpc_attach_answers rest ss) (lpc_projected_rel filtering R) t final"
proof (rule lpc_return_split_lower[where rep=rep and R="lpc_projected_rel filtering R"
    and t=t and p=p and ss=ss and ret=ret and final=final and rest=rest,
    OF program lower entry prefix_rep valid separated])
  fix eta assume reached: "(p,ret eta)\<in>(lpc_projected_rel filtering R)\<^sup>*"
  have observed: "lpc_observed filtering (ret eta)"
    by (rule lpc_projected_reachable_observed[OF reached initial])
  show "\<exists>v. (ret eta,v)\<in>(lpc_projected_rel filtering R)\<^sup>* \<and>
    rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] v final"
    by (rule continuation[OF reached observed])
qed

end
