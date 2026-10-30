theory LP_Answer_Composition
 imports LP_Answer_Contracts
begin


text \<open>Appending a separately checked continuation is valid when a prefix
step either retains that continuation or discards it completely. The invariant
is supplied by the source language (cut-scope ownership for Prolog).\<close>
theorem lp_answer_contract_append:
  assumes prefix: "lp_answer_contract T ss R t ret"
    and suffix: "lp_answer_contract T es R t ret"
    and invariant: "K ss"
    and preserved: "\<And>us event vs. K us \<Longrightarrow> T us event vs \<Longrightarrow> K vs"
    and reflect: "\<And>us event result. us\<noteq>[] \<Longrightarrow> K us \<Longrightarrow>
      T (us@es) event result \<Longrightarrow>
      \<exists>vs. T us event vs \<and> (result=vs@es \<or> result=vs)"
  shows "lp_answer_contract T (ss@es) R t ret"
proof -
  have all: "K us \<longrightarrow> lp_answer_contract T us R t ret \<longrightarrow>
      lp_answer_contract T (us@es) R t ret"
    if sn: "SN_on (lp_answer_steps T) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro impI)
    fix us
    assume ih: "\<And>vs. (us,vs)\<in>lp_answer_steps T \<Longrightarrow>
        K vs \<longrightarrow> lp_answer_contract T vs R t ret \<longrightarrow>
        lp_answer_contract T (vs@es) R t ret"
      and known: "K us" and contract: "lp_answer_contract T us R t ret"
    show "lp_answer_contract T (us@es) R t ret"
    proof (cases "us=[]")
      case True then show ?thesis using suffix by simp
    next
      case False
      show ?thesis
      proof (rule lp_answer_contract_intro)
        fix event result assume step: "T (us@es) event result"
        obtain vs where local: "T us event vs" and shape: "result=vs@es \<or> result=vs"
          using reflect[OF False known step] by blast
        have edge: "(us,vs)\<in>lp_answer_steps T" using local by (auto simp: lp_answer_steps_def)
        have child: "lp_answer_contract T vs R t ret"
          by (rule lp_answer_contract_child[OF contract local])
        have joined: "lp_answer_contract T (vs@es) R t ret"
          using ih[OF edge] preserved[OF known local] child by blast
        have event: "\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*"
          using contract local by (auto simp: lp_answer_contract_def lp_answers_covered_def)
        show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
          lp_answer_contract T result R t ret" using shape child joined event by blast
      qed
    qed
  qed
  show ?thesis using all prefix invariant by (auto simp: lp_answer_contract_def)
qed


theorem lp_answer_contract_simulation:
  fixes T :: "'s \<Rightarrow> 'a option \<Rightarrow> 's \<Rightarrow> bool"
    and V :: "'u \<Rightarrow> 'b option \<Rightarrow> 'u \<Rightarrow> bool"
    and target :: "'u"
  assumes contract: "lp_answer_contract T ss R t ret"
    and represented: "rep ss target"
    and simulate: "\<And>us vs event ws. rep us vs \<Longrightarrow> V vs event ws \<Longrightarrow>
      \<exists>ev zs. T us ev zs \<and> rep zs ws \<and>
        (\<forall>beta. event = Some beta \<longrightarrow> (\<exists>alpha. ev = Some alpha \<and> outputs alpha beta))"
    and bridge: "\<And>alpha beta. outputs alpha beta \<Longrightarrow> (ret alpha,final beta)\<in>R\<^sup>*"
  shows "lp_answer_contract V target R t final"
proof -
  have all: "\<forall>vs. rep us vs \<longrightarrow> lp_answer_contract T us R t ret \<longrightarrow>
      lp_answer_contract V vs R t final"
    if sn: "SN_on (lp_answer_steps T) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix us vs
    assume ih: "\<And>zs. (us,zs)\<in>lp_answer_steps T \<Longrightarrow>
      \<forall>ws. rep zs ws \<longrightarrow> lp_answer_contract T zs R t ret \<longrightarrow>
      lp_answer_contract V ws R t final"
      and known: "rep us vs" and current: "lp_answer_contract T us R t ret"
    show "lp_answer_contract V vs R t final"
    proof (rule lp_answer_contract_intro)
      fix event ws assume step: "V vs event ws"
      obtain ev zs where local: "T us ev zs" and target: "rep zs ws"
        and emitted: "\<forall>beta. event = Some beta \<longrightarrow>
          (\<exists>alpha. ev = Some alpha \<and> outputs alpha beta)"
        using simulate[OF known step] by (elim exE conjE) blast
      have edge: "(us,zs)\<in>lp_answer_steps T" using local by (auto simp: lp_answer_steps_def)
      have child: "lp_answer_contract T zs R t ret"
        by (rule lp_answer_contract_child[OF current local])
      have transferred: "lp_answer_contract V ws R t final"
        using ih[OF edge] target child by blast
      have coverage: "\<forall>beta. event = Some beta \<longrightarrow> (t,final beta)\<in>R\<^sup>*"
      proof (intro allI impI)
        fix beta assume "event = Some beta"
        then obtain alpha where produced: "ev = Some alpha" "outputs alpha beta"
          using emitted by blast
        have prefix: "(t,ret alpha)\<in>R\<^sup>*"
          using current local produced by (auto simp: lp_answer_contract_def lp_answers_covered_def)
        show "(t,final beta)\<in>R\<^sup>*" by (rule rtrancl_trans[OF prefix bridge[OF produced(2)]])
      qed
      show "(\<forall>rho. event = Some rho \<longrightarrow> (t,final rho)\<in>R\<^sup>*) \<and>
        lp_answer_contract V ws R t final" using coverage transferred by blast
    qed
  qed
  show ?thesis using all contract represented by (auto simp: lp_answer_contract_def)
qed

end
