theory LP_Answer_Contracts
  imports LP_Answer_Graph
begin

text \<open>Reusable termination-and-answer contracts for an arbitrary ordered
transition system. Source-language instrumentation is a separate instantiation;
modular descent and silent-suffix composition do not depend on Prolog builtins.\<close>

definition lp_answers_covered where
  "lp_answers_covered T ss C = (\<forall>us rho vs.
    (ss,us)\<in>(lp_answer_steps T)\<^sup>* \<longrightarrow> T us (Some rho) vs \<longrightarrow> C rho)"

lemma lp_answers_covered_event:
  "lp_answers_covered T ss C \<Longrightarrow> T ss (Some rho) tt \<Longrightarrow> C rho"
  by (auto simp: lp_answers_covered_def)

lemma lp_answers_covered_child:
  assumes covered: "lp_answers_covered T ss C" and step: "T ss event tt"
  shows "lp_answers_covered T tt C"
proof (unfold lp_answers_covered_def, intro allI impI)
  fix us rho vs
  assume path: "(tt,us)\<in>(lp_answer_steps T)\<^sup>*" and event: "T us (Some rho) vs"
  have edge: "(ss,tt)\<in>lp_answer_steps T" using step by (auto simp: lp_answer_steps_def)
  have "(ss,us)\<in>(lp_answer_steps T)\<^sup>*"
    by (rule converse_rtrancl_into_rtrancl[OF edge path])
  then show "C rho" using covered event by (auto simp: lp_answers_covered_def)
qed

lemma lp_answers_covered_intro:
  assumes local: "\<And>event tt. T ss event tt \<Longrightarrow>
    (\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> lp_answers_covered T tt C"
  shows "lp_answers_covered T ss C"
proof (unfold lp_answers_covered_def, intro allI impI)
  fix us rho vs
  assume path: "(ss,us)\<in>(lp_answer_steps T)\<^sup>*" and event: "T us (Some rho) vs"
  from path show "C rho"
  proof (cases rule: converse_rtranclE)
    case base then show ?thesis using local event by blast
  next
    case (step tt)
    obtain e where selected: "T ss e tt" using step by (auto simp: lp_answer_steps_def)
    show ?thesis using local[OF selected] step event by (auto simp: lp_answers_covered_def)
  qed
qed

definition lp_answer_contract where
  "lp_answer_contract T ss R t ret = (SN_on (lp_answer_steps T) {ss} \<and>
    lp_answers_covered T ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*))"

lemma lp_answer_contract_intro:
  assumes local: "\<And>event tt. T ss event tt \<Longrightarrow>
    (\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
    lp_answer_contract T tt R t ret"
  shows "lp_answer_contract T ss R t ret"
proof -
  have sn: "SN_on (lp_answer_steps T) {ss}"
    by (rule step_reflects_SN_on)
      (use local in \<open>auto simp: lp_answer_steps_def lp_answer_contract_def\<close>)
  have covered: "lp_answers_covered T ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
    by (rule lp_answers_covered_intro)
      (use local in \<open>auto simp: lp_answer_contract_def\<close>)
  show ?thesis using sn covered by (simp add: lp_answer_contract_def)
qed

lemma lp_answer_contract_child:
  assumes contract: "lp_answer_contract T ss R t ret" and step: "T ss event tt"
  shows "lp_answer_contract T tt R t ret"
proof -
  have edge: "(ss,tt)\<in>lp_answer_steps T" using step by (auto simp: lp_answer_steps_def)
  have parent: "SN_on (lp_answer_steps T) {ss}"
    using contract by (simp add: lp_answer_contract_def)
  have included: "{tt}\<subseteq>(lp_answer_steps T)\<^sup>* `` {ss}"
    using edge by auto
  have sn: "SN_on (lp_answer_steps T) {tt}"
    by (rule SN_on_subset2[OF included SN_on_Image_rtrancl[OF parent]])
  have covered: "lp_answers_covered T ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
    using contract by (simp add: lp_answer_contract_def)
  have child: "lp_answers_covered T tt (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
    by (rule lp_answers_covered_child[where T=T, OF covered step])
  show ?thesis using sn child by (simp add: lp_answer_contract_def)
qed

lemma lp_answer_contract_start:
  "(t,u)\<in>R\<^sup>* \<Longrightarrow> lp_answer_contract T ss R u ret \<Longrightarrow>
    lp_answer_contract T ss R t ret"
  unfolding lp_answer_contract_def lp_answers_covered_def
  by (meson rtrancl_trans)

theorem lp_answer_contract_modular:
  assumes residual: "SN_on R {t}" and represented: "rep ss t ret"
    and local: "\<And>us u retfun. rep us u retfun \<Longrightarrow>
      (\<And>vs v out. (u,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
        lp_answer_contract T vs R v out) \<Longrightarrow>
      lp_answer_contract T us R u retfun"
  shows "lp_answer_contract T ss R t ret"
proof -
  have all: "\<forall>us retfun. rep us u retfun \<longrightarrow> lp_answer_contract T us R u retfun"
    if sn: "SN_on R {u}" for u
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI], intro allI impI)
    fix u us retfun
    assume ih: "\<And>v. (u,v)\<in>R\<^sup>+ \<Longrightarrow>
      \<forall>vs out. rep vs v out \<longrightarrow> lp_answer_contract T vs R v out"
      and rep: "rep us u retfun"
    show "lp_answer_contract T us R u retfun"
      by (rule local[OF rep]) (use ih in blast)
  qed
  show ?thesis using all[OF residual] represented by blast
qed

lemma lp_answer_contract_primitive:
  assumes lower: "\<And>vs v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
      lp_answer_contract T vs R v out"
    and local: "\<And>event tt. T ss event tt \<Longrightarrow>
      (\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u ret) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*)"
  shows "lp_answer_contract T ss R t ret"
proof (rule lp_answer_contract_intro)
  fix event tt assume event: "T ss event tt"
  obtain u where strict: "(t,u)\<in>R\<^sup>+" and represented: "rep tt u ret"
    using local[OF event] by blast
  have child: "lp_answer_contract T tt R t ret"
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict represented]])
  show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract T tt R t ret"
    using local[OF event] child by blast
qed

theorem lp_answer_contract_append_silent:
  assumes contract: "lp_answer_contract T ss R t ret" and tail: "K bs"
    and empty: "\<And>cs. K cs \<Longrightarrow> lp_answer_contract T cs R t ret"
    and drop: "\<And>cs n. K cs \<Longrightarrow> K (drop n cs)"
    and suffix: "\<And>us cs event result. us\<noteq>[] \<Longrightarrow> T (us@cs) event result \<Longrightarrow>
      \<exists>vs n. T us event vs \<and> result=vs@drop n cs"
  shows "lp_answer_contract T (ss@bs) R t ret"
proof -
  have all: "lp_answer_contract T us R t ret \<longrightarrow>
      (\<forall>cs. K cs \<longrightarrow> lp_answer_contract T (us@cs) R t ret)"
    if sn: "SN_on (lp_answer_steps T) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro impI allI impI)
    fix us cs
    assume ih: "\<And>vs. (us,vs)\<in>lp_answer_steps T \<Longrightarrow>
      lp_answer_contract T vs R t ret \<longrightarrow>
      (\<forall>ds. K ds \<longrightarrow> lp_answer_contract T (vs@ds) R t ret)"
      and parent: "lp_answer_contract T us R t ret" and cs: "K cs"
    show "lp_answer_contract T (us@cs) R t ret"
    proof (cases "us=[]")
      case True then show ?thesis using empty[OF cs] by simp
    next
      case False
      show ?thesis
      proof (rule lp_answer_contract_intro)
        fix event result assume step: "T (us@cs) event result"
        obtain vs n where local: "T us event vs" and result: "result=vs@drop n cs"
          using suffix[OF False step] by blast
        have edge: "(us,vs)\<in>lp_answer_steps T" using local by (auto simp: lp_answer_steps_def)
        have child: "lp_answer_contract T vs R t ret" by (rule lp_answer_contract_child[OF parent local])
        have joined: "lp_answer_contract T result R t ret"
          using ih[OF edge] child drop[OF cs] by (simp add: result)
        show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
          lp_answer_contract T result R t ret"
          using joined parent local lp_answers_covered_event by (auto simp: lp_answer_contract_def)
      qed
    qed
  qed
  show ?thesis using all contract tail by (auto simp: lp_answer_contract_def)
qed

lemma lp_answer_contract_reflect:
  fixes T :: "'s \<Rightarrow> 'a option \<Rightarrow> 's \<Rightarrow> bool" and f :: "'s\<Rightarrow>'s"
  assumes contract: "lp_answer_contract T (f ss) R t ret"
    and map_step: "\<And>us event vs. T us event vs \<Longrightarrow> T (f us) event (f vs)"
  shows "lp_answer_contract T ss R t ret"
proof -
  have reflect: "\<forall>us::'s. f us=u \<longrightarrow> SN_on (lp_answer_steps T) {us}"
    if sn: "SN_on (lp_answer_steps T) {u}" for u
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix u and us :: 's
    assume ih: "\<And>v. (u,v)\<in>lp_answer_steps T \<Longrightarrow>
      \<forall>vs::'s. f vs=v \<longrightarrow> SN_on (lp_answer_steps T) {vs}"
      and shape: "f us=u"
    show "SN_on (lp_answer_steps T) {us}"
    proof (rule step_reflects_SN_on)
      fix vs assume "(us,vs)\<in>lp_answer_steps T"
      then have "(u,f vs)\<in>lp_answer_steps T"
        using map_step shape by (auto simp: lp_answer_steps_def)
      then show "SN_on (lp_answer_steps T) {vs}" using ih by blast
    qed
  qed
  have sn: "SN_on (lp_answer_steps T) {ss}"
    using reflect contract by (auto simp: lp_answer_contract_def)
  have path: "(f us,f vs)\<in>(lp_answer_steps T)\<^sup>*"
    if "(us,vs)\<in>(lp_answer_steps T)\<^sup>*" for us vs
    using that by (induct rule: rtrancl_induct)
      (auto simp: lp_answer_steps_def intro: rtrancl_into_rtrancl dest: map_step)
  have covered: "lp_answers_covered T ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
    using contract path map_step unfolding lp_answer_contract_def lp_answers_covered_def by blast
  show ?thesis using sn covered by (simp add: lp_answer_contract_def)
qed

theorem lp_answer_contract_singletons:
  assumes singletons: "\<And>e. e\<in>set ss \<Longrightarrow> lp_answer_contract T [e] R t ret"
    and empty: "lp_answer_contract T [] R t ret"
    and suffix: "\<And>us cs event result. us\<noteq>[] \<Longrightarrow> T (us@cs) event result \<Longrightarrow>
      \<exists>vs n. T us event vs \<and> result=vs@drop n cs"
  shows "lp_answer_contract T ss R t ret"
proof -
  have all: "\<And>n. lp_answer_contract T (drop n ss) R t ret"
    using singletons
  proof (induct ss)
    case Nil then show ?case using empty by simp
  next
    case (Cons e es)
    have tail: "\<And>n. lp_answer_contract T (drop n es) R t ret"
      by (rule Cons.hyps) (use Cons.prems in auto)
    show ?case
    proof (cases n)
      case 0
      have head: "lp_answer_contract T [e] R t ret" using Cons.prems by auto
      have joined: "lp_answer_contract T ([e]@es) R t ret"
      proof (rule lp_answer_contract_append_silent[OF head, where K="\<lambda>cs. \<exists>n. cs=drop n es"])
        show "\<exists>n. es=drop n es" by (rule exI[of _ 0]) simp
        show "\<And>cs. (\<exists>n. cs=drop n es) \<Longrightarrow> lp_answer_contract T cs R t ret"
          using tail by blast
        show "\<And>cs n. (\<exists>m. cs=drop m es) \<Longrightarrow> \<exists>m. drop n cs=drop m es"
          by (auto simp: drop_drop)
        show "\<And>us cs event result. us\<noteq>[] \<Longrightarrow> T (us@cs) event result \<Longrightarrow>
          \<exists>vs n. T us event vs \<and> result=vs@drop n cs" by (rule suffix)
      qed
      show ?thesis using joined by (simp add: 0)
    next
      case (Suc n) then show ?thesis using tail by simp
    qed
  qed
  show ?thesis using all[of 0] by simp
qed

end
