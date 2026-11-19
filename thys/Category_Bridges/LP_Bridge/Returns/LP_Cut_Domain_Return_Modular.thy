theory LP_Cut_Domain_Return_Modular
  imports LP_Cut_Domain_Return_Coverage
begin

context cut_runtime_domain
begin

theorem precise_return_contract_modular:
  assumes residual: "SN_on R {t}"
    and represented: "rep ss t ret"
    and local: "\<And>us u retfun. rep us u retfun \<Longrightarrow>
      (\<And>vs v out. (u,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
        precise_return_contract P vs R v out) \<Longrightarrow>
      precise_return_contract P us R u retfun"
  shows "precise_return_contract P ss R t ret"
proof -
  have all: "\<forall>us retfun. rep us u retfun \<longrightarrow> precise_return_contract P us R u retfun"
    if sn: "SN_on R {u}" for u
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI], intro allI impI)
    fix u us retfun
    assume ih: "\<And>v. (u,v)\<in>R\<^sup>+ \<Longrightarrow>
      \<forall>vs out. rep vs v out \<longrightarrow> precise_return_contract P vs R v out"
      and rep: "rep us u retfun"
    show "precise_return_contract P us R u retfun"
      by (rule local[OF rep]) (use ih in blast)
  qed
  show ?thesis using all[OF residual] represented by blast
qed

lemma precise_return_contract_start:
  assumes path: "(t,u)\<in>R\<^sup>*"
    and child: "precise_return_contract P ss R u ret"
  shows "precise_return_contract P ss R t ret"
proof (unfold precise_return_contract_def, intro conjI allI impI)
  show "SN_on (precise_source P) {map fst ss}"
    using child by (simp add: precise_return_contract_def)
next
  fix us vs rho
  assume reached: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some rho) vs"
  have tail: "(u,ret rho)\<in>R\<^sup>*"
    using child reached event unfolding precise_return_contract_def by blast
  show "(t,ret rho)\<in>R\<^sup>*" by (rule rtrancl_trans[OF path tail])
qed

theorem precise_return_primitive_lower:
  assumes lower: "\<And>vs v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
      precise_return_contract P vs R v out"
    and local: "\<And>event tt. precise_answer_transition P ss event tt \<Longrightarrow>
      (\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u ret) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*)"
  shows "precise_return_contract P ss R t ret"
proof -
  have sn: "SN_on (precise_answer_steps P) {ss}"
  proof (rule step_reflects_SN_on)
    fix tt assume edge: "(ss,tt)\<in>precise_answer_steps P"
    obtain event where event: "precise_answer_transition P ss event tt"
      using edge by (auto simp: precise_answer_steps_def)
    obtain u where strict: "(t,u)\<in>R\<^sup>+" and rep: "rep tt u ret"
      using local[OF event] by blast
    have contract: "precise_return_contract P tt R u ret" by (rule lower[OF strict rep])
    show "SN_on (precise_answer_steps P) {tt}"
      using contract by (simp add: precise_return_contract_def precise_answer_instrumentation_SN)
  qed
  have answers: "precise_answers_covered P ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
  proof (rule precise_answers_covered_intro)
    fix event tt assume event: "precise_answer_transition P ss event tt"
    obtain u where strict: "(t,u)\<in>R\<^sup>+" and rep: "rep tt u ret"
      using local[OF event] by blast
    have contract: "precise_return_contract P tt R t ret"
      by (rule precise_return_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict rep]])
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      precise_answers_covered P tt (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
      using local[OF event] contract unfolding precise_return_contract_def precise_answers_covered_def by auto
  qed
  show ?thesis using sn answers
    by (auto simp: precise_return_contract_def precise_answers_covered_def precise_answer_instrumentation_SN)
qed


end
end
