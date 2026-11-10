theory LP_Prolog_Return_Modular
  imports LP_Answer_Contracts LP_Prolog_Return_Check LP_Cut_Return_Barriers
begin

lemma lpp_answer_erased_SN:
  fixes P :: "('f,string) lp_cut_program"
    and ss :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
  assumes source: "SN_on (lpp_atomic_source P B U) {map fst ss}"
  shows "SN_on (lp_answer_steps (lpp_answer_transition P B U)) {ss}"
proof -
  have all: "\<forall>ss::(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times> ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list. map fst ss=s \<longrightarrow>
      SN_on (lp_answer_steps (lpp_answer_transition P B U)) {ss}"
    if sn: "SN_on (lpp_atomic_source P B U) {s}" for s
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix s and ss :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
    assume ih: "\<And>t. (s,t)\<in>lpp_atomic_source P B U \<Longrightarrow>
      \<forall>tt::(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times> ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list. map fst tt=t \<longrightarrow> SN_on (lp_answer_steps (lpp_answer_transition P B U)) {tt}"
      and shape: "map fst ss=s"
    show "SN_on (lp_answer_steps (lpp_answer_transition P B U)) {ss}"
    proof (rule step_reflects_SN_on)
      fix tt assume "(ss,tt)\<in>lp_answer_steps (lpp_answer_transition P B U)"
      then obtain event where step: "lpp_answer_transition P B U ss event tt"
        by (auto simp: lp_answer_steps_def)
      have edge: "(s,map fst tt)\<in>lpp_atomic_source P B U"
        using lpp_answer_transition_erases[OF step] by (simp add: shape)
      show "SN_on (lp_answer_steps (lpp_answer_transition P B U)) {tt}"
        using ih[OF edge] by blast
    qed
  qed
  show ?thesis using all[OF source] by blast
qed

lemma lpp_return_as_answer_contract:
  "lpp_return_contract P B U ss R t ret =
    lp_answer_contract (lpp_answer_transition P B U) ss R t ret"
  unfolding lpp_return_contract_def lp_answer_contract_def lp_answers_covered_def
  using lpp_answer_erased_SN lpp_answer_instrumentation_SN by blast

text \<open>The ordinary LP-with-cut contract is an instance of the same
language-independent modular infrastructure; no second graph semantics is
introduced for Prolog.\<close>
lemma lpc_return_as_answer_contract:
  "lpc_return_contract P ss R t ret =
    lp_answer_contract (lpc_answer_transition P) ss R t ret"
proof -
  have steps: "lp_answer_steps (lpc_answer_transition P)=lpc_answer_steps P"
    by (simp add: lp_answer_steps_def lpc_answer_steps_def)
  show ?thesis by (auto simp: lpc_return_contract_def lp_answer_contract_def
    lp_answers_covered_def steps lpc_answer_instrumentation_SN)
qed

lemma lpp_builtin_active_append:
  "ss\<noteq>[] \<Longrightarrow>
    lpp_builtin_active B (map fst (ss@bs)) = lpp_builtin_active B (map fst ss)"
  by (cases ss) (auto simp: lpp_builtin_active_def)

lemma lpp_answer_append_suffix:
  assumes nonempty: "ss\<noteq>[]" and step: "lpp_answer_transition P B U (ss@bs) event result"
  shows "\<exists>tt n. lpp_answer_transition P B U ss event tt \<and> result=tt@drop n bs"
proof -
  obtain e eta tail where ss: "ss=(e,eta)#tail"
    using nonempty by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof (cases rule: lpp_answer_transition.cases)
    case base
    obtain tt n where local: "lpc_answer_transition P ss event tt" and result: "result=tt@drop n bs"
      using lpc_answer_append_suffix[OF nonempty base(2)] by blast
    have clear: "\<not>lpp_builtin_active B (map fst ss)"
      using base(1) lpp_builtin_active_append[OF nonempty] by blast
    show ?thesis using lpp_answer_transition.base[OF clear local] result by blast
  next
    case error
    then show ?thesis using ss
      by (force intro: exI[of _ "length bs"] lpp_answer_transition.error)
  next
    case (probe f ts a keep m gs es n rho)
    have shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)"
      "rho=eta" "es=tail@bs"
      using probe(1) ss by auto
    have fm: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst tail)"
      using probe(5) shape by (auto simp: lp_cut_fresh_def)
    have fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst tail)"
      using probe(6) shape by (auto simp: lp_cut_fresh_def)
    have local: "lpp_answer_transition P B U
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#tail) None
      ((LPCGoals (lpp_probe_goals a keep m gs),eta)#(LPCBarrier n,eta)#
        (LPCGoals (lpp_probe_else keep gs),eta)#(LPCBarrier m,eta)#tail)"
      by (rule lpp_answer_transition.probe) (rule probe(4), rule fm, rule fn)
    show ?thesis using local probe(2,3) shape ss
      by (intro exI[of _ "(LPCGoals (lpp_probe_goals a keep m gs),eta)#(LPCBarrier n,eta)#
        (LPCGoals (lpp_probe_else keep gs),eta)#(LPCBarrier m,eta)#tail"] exI[of _ 0]) simp
  next
    case (branch f ts cs ys ns m gs es n rho)
    have shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)"
      "rho=eta" "es=tail@bs"
      using branch(1) ss by auto
    have fm: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst tail)"
      using branch(6) shape by (auto simp: lp_cut_fresh_def)
    have fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst tail)"
      using branch(7) shape by (auto simp: lp_cut_fresh_def)
    have local: "lpp_answer_transition P B U
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#tail) None
      ((LPCGoals (cs@(LPCCut m#(ys@gs))),eta)#(LPCBarrier n,eta)#
        (LPCGoals (ns@gs),eta)#(LPCBarrier m,eta)#tail)"
      by (rule lpp_answer_transition.branch) (rule branch(4), rule branch(5), rule fm, rule fn)
    show ?thesis using local branch(2,3) shape ss
      by (intro exI[of _ "(LPCGoals (cs@(LPCCut m#(ys@gs))),eta)#(LPCBarrier n,eta)#
        (LPCGoals (ns@gs),eta)#(LPCBarrier m,eta)#tail"] exI[of _ 0]) simp
  qed (use ss in \<open>force intro: exI[of _ 0] lpp_answer_transition.intros\<close>)+
qed

lemma lpp_barriers_answer_contract:
  "lp_cut_barriers (map fst bs) \<Longrightarrow>
    lp_answer_contract (lpp_answer_transition P B U) bs R t ret"
proof (induct bs)
  case Nil
  show ?case by (rule lp_answer_contract_intro)
    (auto elim: lpp_answer_transition.cases lpc_answer_transition.cases)
next
  case (Cons frame bs)
  obtain m eta where frame: "frame=(LPCBarrier m,eta)"
    using Cons.prems by (cases frame; cases "fst frame"; auto)
  have tail: "lp_answer_contract (lpp_answer_transition P B U) bs R t ret"
    using Cons by (simp add: frame)
  show ?case by (rule lp_answer_contract_intro)
    (use tail in \<open>auto simp: frame elim: lpp_answer_transition.cases lpc_answer_transition.cases\<close>)
qed

theorem lpp_return_contract_append_barriers:
  assumes contract: "lpp_return_contract P B U ss R t ret"
    and barriers: "lp_cut_barriers (map fst bs)"
  shows "lpp_return_contract P B U (ss@bs) R t ret"
  unfolding lpp_return_as_answer_contract
proof (rule lp_answer_contract_append_silent[where K="\<lambda>bs. lp_cut_barriers (map fst bs)"])
  show "lp_answer_contract (lpp_answer_transition P B U) ss R t ret"
    using contract by (simp add: lpp_return_as_answer_contract)
  show "lp_cut_barriers (map fst bs)" by (rule barriers)
  show "\<And>cs. lp_cut_barriers (map fst cs) \<Longrightarrow>
    lp_answer_contract (lpp_answer_transition P B U) cs R t ret"
    by (rule lpp_barriers_answer_contract)
  show "\<And>cs n. lp_cut_barriers (map fst cs) \<Longrightarrow> lp_cut_barriers (map fst (drop n cs))"
    by (auto simp: list_all_iff dest: in_set_dropD)
  show "\<And>us cs event result. us\<noteq>[] \<Longrightarrow>
    lpp_answer_transition P B U (us@cs) event result \<Longrightarrow>
    \<exists>vs n. lpp_answer_transition P B U us event vs \<and> result=vs@drop n cs"
    by (rule lpp_answer_append_suffix)
qed

theorem lpp_return_contract_scopes:
  assumes program: "lp_cut_source_program P" and contract: "lpp_return_contract P B U ss R t ret"
  shows "lpp_return_contract P B U (lpc_return_scope_word swaps ss) R t ret"
  unfolding lpp_return_as_answer_contract
proof (rule lp_answer_contract_reflect[where f="lpc_return_scope_word (rev swaps)"])
  show "lp_answer_contract (lpp_answer_transition P B U)
    (lpc_return_scope_word (rev swaps) (lpc_return_scope_word swaps ss)) R t ret"
    using contract by (simp add: lpp_return_as_answer_contract lpc_return_scope_word_inverse)
  show "\<And>us event vs. lpp_answer_transition P B U us event vs \<Longrightarrow>
    lpp_answer_transition P B U (lpc_return_scope_word (rev swaps) us) event
      (lpc_return_scope_word (rev swaps) vs)"
    by (rule lpp_answer_transition_scope_word[OF _ program])
qed

theorem lpp_return_contract_singletons:
  assumes singletons: "\<And>e. e\<in>set ss \<Longrightarrow> lpp_return_contract P B U [e] R t ret"
  shows "lpp_return_contract P B U ss R t ret"
  unfolding lpp_return_as_answer_contract
proof (rule lp_answer_contract_singletons)
  show "\<And>e. e\<in>set ss \<Longrightarrow> lp_answer_contract (lpp_answer_transition P B U) [e] R t ret"
    using singletons by (simp add: lpp_return_as_answer_contract)
  show "lp_answer_contract (lpp_answer_transition P B U) [] R t ret"
    by (rule lpp_barriers_answer_contract) simp
  show "\<And>us cs event result. us\<noteq>[] \<Longrightarrow>
    lpp_answer_transition P B U (us@cs) event result \<Longrightarrow>
    \<exists>vs n. lpp_answer_transition P B U us event vs \<and> result=vs@drop n cs"
    by (rule lpp_answer_append_suffix)
qed

end
