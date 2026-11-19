theory LP_Cut_Domain_SEG_TRS_Returns
 imports Category_LP_Library.LP_Cut_SEG_Free_Certificate_XML Category_LP_Library.LP_Cut_SEG_Projected_Certificate_XML Category_LP_Library.LP_Cut_SEG_Triple_XML Category_LP_Cut_Projected_Bridge.LP_Cut_Domain_Projected_Checker
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_seg_primitive_contract:
  assumes children: "\<And>event tt. precise_answer_transition P ss event tt \<Longrightarrow>
      precise_return_contract P tt R t ret"
    and answers: "\<And>rho tt. precise_answer_transition P ss (Some rho) tt \<Longrightarrow>
      (t,ret rho)\<in>R\<^sup>*"
  shows "precise_return_contract P ss R t ret"
proof -
  have sn: "SN_on (precise_answer_steps P) {ss}"
  proof (rule step_reflects_SN_on)
    fix tt assume edge: "(ss,tt)\<in>precise_answer_steps P"
    obtain event where event: "precise_answer_transition P ss event tt"
      using edge by (auto simp: precise_answer_steps_def)
    show "SN_on (precise_answer_steps P) {tt}"
      using children[OF event]
      by (simp add: precise_return_contract_def precise_answer_instrumentation_SN)
  qed
  have covered: "precise_answers_covered P ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
  proof (rule precise_answers_covered_intro)
    fix event tt assume event: "precise_answer_transition P ss event tt"
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      precise_answers_covered P tt (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
      using children[OF event] answers event
      unfolding precise_return_contract_def precise_answers_covered_def by blast
  qed
  show ?thesis using sn covered
    by (auto simp: precise_return_contract_def precise_answers_covered_def precise_answer_instrumentation_SN)
qed


theorem precise_seg_connection_region:
  fixes rank :: "'a \<Rightarrow> nat"
  assumes represented: "region node ss t ret"
    and boundary: "\<And>i us u out event vs. region i us u out \<Longrightarrow>
      precise_answer_transition P us event vs \<Longrightarrow>
      (\<exists>j. rank j < rank i \<and> region j vs u out) \<or>
      precise_return_contract P vs R u out"
    and answers: "\<And>i us u out rho vs. region i us u out \<Longrightarrow>
      precise_answer_transition P us (Some rho) vs \<Longrightarrow> (u,out rho)\<in>R\<^sup>*"
  shows "precise_return_contract P ss R t ret"
proof -
  have all: "\<And>ss t ret. region i ss t ret \<Longrightarrow> precise_return_contract P ss R t ret" for i
  proof (induction i rule: measure_induct_rule[of rank])
    case (less i)
    show ?case
    proof (rule precise_seg_primitive_contract)
      fix event vs assume event: "precise_answer_transition P ss event vs"
      show "precise_return_contract P vs R t ret"
        using boundary[OF less.prems event] less.IH by blast
    next
      fix rho vs assume event: "precise_answer_transition P ss (Some rho) vs"
      show "(t,ret rho)\<in>R\<^sup>*" by (rule answers[OF less.prems event])
    qed
  qed
  show ?thesis by (rule all[OF represented])
qed


theorem precise_seg_modular_connection_regions:
  fixes rank :: "'a \<Rightarrow> nat"
  assumes sn: "SN_on R {t}"
    and initial: "rep ss t ret"
    and root: "\<And>us u out. rep us u out \<Longrightarrow> \<exists>i. region i us u out"
    and edges: "\<And>i us u out event vs. region i us u out \<Longrightarrow>
      precise_answer_transition P us event vs \<Longrightarrow>
      (\<exists>j. rank j < rank i \<and> region j vs u out) \<or>
      (\<exists>v. (u,v)\<in>R\<^sup>+ \<and> rep vs v out)"
    and answers: "\<And>i us u out rho vs. region i us u out \<Longrightarrow>
      precise_answer_transition P us (Some rho) vs \<Longrightarrow> (u,out rho)\<in>R\<^sup>*"
  shows "precise_return_contract P ss R t ret"
proof (rule precise_return_contract_modular[where rep=rep, OF sn initial])
  fix us u out
  assume represented: "rep us u out"
    and lower: "\<And>vs v final. (u,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v final \<Longrightarrow>
      precise_return_contract P vs R v final"
  obtain i where entry: "region i us u out" using root[OF represented] by blast
  show "precise_return_contract P us R u out"
  proof (rule precise_seg_connection_region[where region="\<lambda>j xs v f. region j xs v f \<and> v=u" and rank=rank and node=i])
    show "region i us u out \<and> u=u" using entry by simp
  next
    fix j xs v f event ys
    assume represented: "region j xs v f \<and> v=u"
      and event: "precise_answer_transition P xs event ys"
    have cases: "(\<exists>k. rank k < rank j \<and> region k ys v f) \<or>
      (\<exists>w. (v,w)\<in>R\<^sup>+ \<and> rep ys w f)"
      by (rule edges[OF conjunct1[OF represented] event])
    have boundary: "precise_return_contract P ys R v f"
      if step: "(v,w)\<in>R\<^sup>+" and child: "rep ys w f" for w
    proof -
      have contract: "precise_return_contract P ys R w f"
        using lower[of w ys f] step child represented by simp
      show ?thesis by (rule precise_return_contract_start[OF trancl_into_rtrancl[OF step] contract])
    qed
    show "(\<exists>k. rank k < rank j \<and> (region k ys v f \<and> v=u)) \<or>
      precise_return_contract P ys R v f"
      using cases represented boundary by blast
  next
    fix j xs v f rho ys
    assume represented: "region j xs v f \<and> v=u"
      and event: "precise_answer_transition P xs (Some rho) ys"
    show "(v,f rho)\<in>R\<^sup>*" by (rule answers[OF conjunct1[OF represented] event])
  qed
qed


lemma precise_return_contract_context:
  fixes C :: "('g,'w) ctxt"
  assumes closed: "ctxt.closed R"
    and contract: "precise_return_contract P ss R t ret"
  shows "precise_return_contract P ss R (C\<langle>t\<rangle>) (\<lambda>eta. C\<langle>ret eta\<rangle>)"
proof (unfold precise_return_contract_def, intro conjI allI impI)
  show "SN_on (precise_source P) {map fst ss}"
    using contract by (simp add: precise_return_contract_def)
next
  fix us tail eta
  assume path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some eta) tail"
  have returned: "(t,ret eta)\<in>R\<^sup>*"
    using contract path event unfolding precise_return_contract_def by blast
  show "(C\<langle>t\<rangle>,C\<langle>ret eta\<rangle>)\<in>R\<^sup>*"
    using returned by (induct rule: rtrancl_induct)
      (auto intro: rtrancl_into_rtrancl ctxt.closedD[OF closed])
qed


lemma precise_return_contract_post_actual:
  assumes contract: "precise_return_contract P ss R t ret"
    and post: "\<And>eta. precise_actual_return P ss eta \<Longrightarrow> (ret eta,final eta)\<in>R\<^sup>*"
  shows "precise_return_contract P ss R t final"
proof (unfold precise_return_contract_def, intro conjI allI impI)
  show "SN_on (precise_source P) {map fst ss}"
    using contract by (simp add: precise_return_contract_def)
next
  fix us tail eta
  assume path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some eta) tail"
  have actual: "precise_actual_return P ss eta"
    using path event unfolding precise_actual_return_def by blast
  have returned: "(t,ret eta)\<in>R\<^sup>*"
    by (rule precise_actual_return_residual[OF contract actual])
  show "(t,final eta)\<in>R\<^sup>*"
    by (rule rtrancl_trans[OF returned post[OF actual]])
qed


theorem precise_seg_trs_split_contract:
  fixes P :: "('f,string) lp_cut_program"
    and C1 :: "('g,'w) ctxt"
    and C2 :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('g,'w) ctxt"
  assumes program: "lp_cut_source_program P"
    and closed: "ctxt.closed R"
    and first: "precise_return_contract P ss R t1 O1"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and entry: "(t,C1\<langle>t1\<rangle>)\<in>R\<^sup>*"
    and second: "\<And>mu. precise_actual_return P ss mu \<Longrightarrow>
      precise_return_contract P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x mu)) rest),mu)]
        R (I2 mu) (O2 mu)"
    and middle: "\<And>mu. precise_actual_return P ss mu \<Longrightarrow>
      (C1\<langle>O1 mu\<rangle>,(C2 mu)\<langle>I2 mu\<rangle>)\<in>R\<^sup>*"
    and finish: "\<And>mu eta. precise_actual_return P ss mu \<Longrightarrow>
      precise_actual_return P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x mu)) rest),mu)] eta \<Longrightarrow>
      ((C2 mu)\<langle>O2 mu eta\<rangle>,ret eta)\<in>R\<^sup>*"
  shows "precise_return_contract P (lpc_attach_answers rest ss) R t ret"
proof -
  have prefix: "precise_return_contract P ss R (C1\<langle>t1\<rangle>) (\<lambda>mu. C1\<langle>O1 mu\<rangle>)"
    by (rule precise_return_contract_context[OF closed first])
  have composed: "precise_return_contract P (lpc_attach_answers rest ss) R (C1\<langle>t1\<rangle>) ret"
  proof (rule precise_return_contract_compose_actual[OF program prefix valid separated])
    fix mu assume actual: "precise_actual_return P ss mu"
    let ?child = "[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x mu)) rest),mu)]"
    have lifted: "precise_return_contract P ?child R ((C2 mu)\<langle>I2 mu\<rangle>)
      (\<lambda>eta. (C2 mu)\<langle>O2 mu eta\<rangle>)"
      by (rule precise_return_contract_context[OF closed second[OF actual]])
    have completed: "precise_return_contract P ?child R ((C2 mu)\<langle>I2 mu\<rangle>) ret"
      by (rule precise_return_contract_post_actual[OF lifted]) (rule finish[OF actual])
    show "precise_return_contract P ?child R (C1\<langle>O1 mu\<rangle>) ret"
      by (rule precise_return_contract_start[OF middle[OF actual] completed])
  qed
  show ?thesis by (rule precise_return_contract_start[OF entry composed])
qed


end
end
