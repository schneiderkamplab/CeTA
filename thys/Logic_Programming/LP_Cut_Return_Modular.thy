theory LP_Cut_Return_Modular
  imports LP_Cut_Return_Attached_Answers
begin

text \<open>Recursive summaries are justified by strict residual descent. The
representation carries its own return interface: different prefix/continuation
modules need not share an arity or a return predicate. No recursive source
termination assumption is admitted at the root.\<close>

theorem lpc_return_contract_modular:
  assumes residual: "SN_on R {t}"
    and represented: "rep ss t ret"
    and local: "\<And>us u retfun. rep us u retfun \<Longrightarrow>
      (\<And>vs v out. (u,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
        lpc_return_contract P vs R v out) \<Longrightarrow>
      lpc_return_contract P us R u retfun"
  shows "lpc_return_contract P ss R t ret"
proof -
  have all: "\<forall>us retfun. rep us u retfun \<longrightarrow> lpc_return_contract P us R u retfun"
    if sn: "SN_on R {u}" for u
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI], intro allI impI)
    fix u us retfun
    assume ih: "\<And>v. (u,v)\<in>R\<^sup>+ \<Longrightarrow>
      \<forall>vs out. rep vs v out \<longrightarrow> lpc_return_contract P vs R v out"
      and rep: "rep us u retfun"
    show "lpc_return_contract P us R u retfun"
      by (rule local[OF rep]) (use ih in blast)
  qed
  show ?thesis using all[OF residual] represented by blast
qed

lemma lpc_return_contract_start:
  assumes path: "(t,u)\<in>R\<^sup>*"
    and child: "lpc_return_contract P ss R u ret"
  shows "lpc_return_contract P ss R t ret"
proof (unfold lpc_return_contract_def, intro conjI allI impI)
  show "SN_on (lp_cut_mgu_source P) {map fst ss}"
    using child by (simp add: lpc_return_contract_def)
next
  fix us vs rho
  assume reached: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some rho) vs"
  have tail: "(u,ret rho)\<in>R\<^sup>*"
    using child reached event unfolding lpc_return_contract_def by blast
  show "(t,ret rho)\<in>R\<^sup>*" by (rule rtrancl_trans[OF path tail])
qed

theorem lpc_return_split_lower:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and lower: "\<And>vs v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
      lpc_return_contract P vs R v out"
    and entry: "(t,p)\<in>R\<^sup>+"
    and prefix_rep: "rep ss p ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation_rep: "\<And>eta. (p,ret eta)\<in>R\<^sup>* \<Longrightarrow> \<exists>v.
      (ret eta,v)\<in>R\<^sup>* \<and>
      rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] v final"
  shows "lpc_return_contract P (lpc_attach_answers rest ss) R t final"
proof -
  have prefix: "lpc_return_contract P ss R p ret"
    by (rule lower[OF entry prefix_rep])
  have combined: "lpc_return_contract P (lpc_attach_answers rest ss) R p final"
  proof (rule lpc_return_contract_compose[OF program prefix valid separated])
    fix eta assume reached: "(p,ret eta)\<in>R\<^sup>*"
    obtain v where bridge: "(ret eta,v)\<in>R\<^sup>*"
      and represented: "rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] v final"
      using continuation_rep[OF reached] by blast
    have suffix: "(p,v)\<in>R\<^sup>*" by (rule rtrancl_trans[OF reached bridge])
    have strict: "(t,v)\<in>R\<^sup>+" by (rule trancl_rtrancl_trancl[OF entry suffix])
    have child: "lpc_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R v final"
      by (rule lower[OF strict represented])
    show "lpc_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
      by (rule lpc_return_contract_start[OF bridge child])
  qed
  show ?thesis by (rule lpc_return_contract_start[OF trancl_into_rtrancl[OF entry] combined])
qed

theorem lpc_return_primitive_lower:
  assumes lower: "\<And>vs v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
      lpc_return_contract P vs R v out"
    and local: "\<And>event tt. lpc_answer_transition P ss event tt \<Longrightarrow>
      (\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u ret) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*)"
  shows "lpc_return_contract P ss R t ret"
proof -
  have sn: "SN_on (lpc_answer_steps P) {ss}"
  proof (rule step_reflects_SN_on)
    fix tt assume edge: "(ss,tt)\<in>lpc_answer_steps P"
    obtain event where event: "lpc_answer_transition P ss event tt"
      using edge by (auto simp: lpc_answer_steps_def)
    obtain u where strict: "(t,u)\<in>R\<^sup>+" and rep: "rep tt u ret"
      using local[OF event] by blast
    have contract: "lpc_return_contract P tt R u ret" by (rule lower[OF strict rep])
    show "SN_on (lpc_answer_steps P) {tt}"
      using contract by (simp add: lpc_return_contract_def lpc_answer_instrumentation_SN)
  qed
  have answers: "lpc_answers_covered P ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
  proof (rule lpc_answers_covered_intro)
    fix event tt assume event: "lpc_answer_transition P ss event tt"
    obtain u where strict: "(t,u)\<in>R\<^sup>+" and rep: "rep tt u ret"
      using local[OF event] by blast
    have contract: "lpc_return_contract P tt R t ret"
      by (rule lpc_return_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict rep]])
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      lpc_answers_covered P tt (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
      using local[OF event] contract unfolding lpc_return_contract_def lpc_answers_covered_def by auto
  qed
  show ?thesis using sn answers
    by (auto simp: lpc_return_contract_def lpc_answers_covered_def lpc_answer_instrumentation_SN)
qed

end
