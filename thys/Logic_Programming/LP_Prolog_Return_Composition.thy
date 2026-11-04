theory LP_Prolog_Return_Composition
  imports LP_Prolog_Return_Modular LP_Cut_Return_Attached_Answers LP_Scoped_Answer_Composition
begin

text \<open>Continuation attachment reuses the cut-aware stack and saved answer
interface. Builtin failure backtracks; builtin error discards the complete stack.
Neither is interpreted as a successful helper return.\<close>

lemma lpp_owned_answer_preserved:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E (map fst ss)"
    and step: "lpp_answer_transition P B U ss event tt"
  shows "lpc_owned_stack E (map fst tt)"
  using step
proof (cases rule: lpp_answer_transition.cases)
  case base
  show ?thesis
    by (rule lpc_owned_source_preserved[OF program owned lpc_answer_transition_erases[OF base(2)]])
qed (use owned in \<open>auto simp: lpc_owned_goals_map lpp_probe_goals_def lpp_probe_else_def lp_cut_fresh_def lpc_owned_fresh_barrier split: if_splits\<close>)

lemma lpp_owned_answer_append:
  assumes nonempty: "ss\<noteq>[]"
    and owned: "lpc_owned_stack E (map fst ss)"
    and separated: "E\<inter>set (lpc_barrier_ids (map fst es)) = {}"
    and step: "lpp_answer_transition P B U (ss@es) event u"
  shows "\<exists>tt. lpp_answer_transition P B U ss event tt \<and> (u = tt@es \<or> u = tt)"
proof -
  obtain e eta tail where ss: "ss = (e,eta)#tail"
    using nonempty by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof (cases rule: lpp_answer_transition.cases)
    case base
    obtain tt where local: "lpc_answer_transition P ss event tt"
      and result: "u = tt@es \<or> u = tt"
      using lpc_owned_answer_append[OF nonempty owned separated base(2)] by blast
    have clear: "\<not>lpp_builtin_active B (map fst ss)"
      using base(1) lpp_builtin_active_append[OF nonempty] by blast
    show ?thesis using lpp_answer_transition.base[OF clear local] result by blast
  next
    case success then show ?thesis using ss
      by (auto intro: lpp_answer_transition.success)
  next
    case failure then show ?thesis using ss
      by (auto intro: lpp_answer_transition.failure)
  next
    case error then show ?thesis using ss
      by (auto intro: lpp_answer_transition.error)
  next
    case (probe f ts a keep m gs saved n rho)
    have shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)"
      "rho=eta" "saved=tail@es"
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
        (LPCGoals (lpp_probe_else keep gs),eta)#(LPCBarrier m,eta)#tail"]) simp
  qed
qed

lemma lpp_clause_nonempty_preserved:
  "lpp_answer_transition P B U ss event tt \<Longrightarrow>
   list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss \<Longrightarrow>
   list_all (\<lambda>x. lpc_clause_nonempty (fst x)) tt"
  by (erule lpp_answer_transition.cases)
    (auto dest: lpc_clause_nonempty_preserved)

lemma lpp_builtin_active_attach:
  assumes active: "lpc_prefix_active ss"
  shows "lpp_builtin_active B (map fst (lpc_attach_answers rest ss)) = lpp_builtin_active B (map fst ss)"
proof -
  obtain e eta es where ss: "ss = (e,eta)#es"
    using active by (cases ss; auto split: prod.splits)
  show ?thesis
  proof (cases e)
    case (LPCGoals gs)
    then show ?thesis using active
      by (cases gs; auto simp: ss lpc_attach_answers_def lpp_builtin_active_def)
  qed (auto simp: ss lpc_attach_answers_def lpp_builtin_active_def)
qed

lemma lpp_attach_answers_active_reflect:
  assumes active: "lpc_prefix_active ss"
    and step: "lpp_answer_transition P B U (lpc_attach_answers rest ss) event u"
  shows "event = None \<and> (\<exists>tt. lpp_answer_transition P B U ss None tt \<and>
    u = lpc_attach_answers rest tt)"
proof -
  obtain e eta es where ss: "ss = (e,eta)#es"
    using active by (cases ss; auto split: prod.splits)
  have goals_shape: "\<exists>prefix. e = LPCGoals (g#prefix) \<and>
      gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest \<and>
      tail = lpc_attach_answers rest es \<and> rho = eta"
    if eq: "lpc_attach_answers rest ss = (LPCGoals (g#gs),rho)#tail"
    for g gs rho tail
  proof (cases e)
    case (LPCGoals xs)
    obtain h prefix where xs: "xs = h#prefix"
      using active ss LPCGoals by (cases xs) auto
    show ?thesis using eq by (auto simp: ss LPCGoals xs lpc_attach_answers_def)
  qed (use eq ss in \<open>auto simp: lpc_attach_answers_def\<close>)
  from step show ?thesis
  proof (cases rule: lpp_answer_transition.cases)
    case base
    obtain tt where silent: "event = None" and local: "lpc_answer_transition P ss None tt"
      and result: "u = lpc_attach_answers rest tt"
      using lpc_attach_answers_active_reflect[OF active base(2)] by blast
    have clear: "\<not>lpp_builtin_active B (map fst ss)"
      using base(1) lpp_builtin_active_attach[OF active] by blast
    show ?thesis using silent result lpp_answer_transition.base[OF clear local] by blast
  next
    case (success f ts sigma gs rho tail)
    obtain prefix where shape: "e = LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
      and tail: "tail = lpc_attach_answers rest es" and rho: "rho = eta"
      using goals_shape success by blast
    have local: "lpp_answer_transition P B U ss None
      ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) prefix),
        \<lambda>x. lp_isubst (eta x) sigma)#es)"
      unfolding ss shape by (rule lpp_answer_transition.success) (use success in auto)
    show ?thesis using success local gs tail rho
      by (auto simp: lpc_attach_answers_def map_map o_def lp_cut_map_comp lp_ieval_subst)
  next
    case (failure f ts gs rho)
    obtain prefix where shape: "e = LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)"
      and result: "u = lpc_attach_answers rest es"
      using goals_shape failure by blast
    have local: "lpp_answer_transition P B U ss None es"
      unfolding ss shape by (rule lpp_answer_transition.failure) (use failure in auto)
    show ?thesis using failure local result by auto
  next
    case (error f ts gs rho tail)
    obtain prefix where shape: "e = LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)"
      using goals_shape error by blast
    have local: "lpp_answer_transition P B U ss None []"
      unfolding ss shape by (rule lpp_answer_transition.error) (use error in auto)
    show ?thesis using error local by (auto simp: lpc_attach_answers_def)
  next
    case (probe f ts a keep m gs saved n rho)
    obtain prefix where shape: "e = LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
      and saved: "saved = lpc_attach_answers rest es" and rho: "rho = eta"
      using goals_shape probe by blast
    have fm0: "lp_cut_fresh m (map fst ss)"
      by (rule lpc_attach_fresh[where rest=rest])
        (use probe in \<open>simp add: lpc_attach_answers_erases[symmetric]\<close>)
    have fn0: "lp_cut_fresh n (map fst ((LPCBarrier m,eta)#ss))"
      by (rule lpc_attach_fresh[where rest=rest])
        (use probe in \<open>simp add: lpc_attach_answers_erases[symmetric]\<close>)
    have fm: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)#map fst es)"
      using fm0 by (simp add: ss shape)
    have fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)#map fst es)"
      using fn0 by (simp add: ss shape)
    have local: "lpp_answer_transition P B U ss None
      ((LPCGoals (lpp_probe_goals a keep m prefix),eta)#(LPCBarrier n,eta)#
        (LPCGoals (lpp_probe_else keep prefix),eta)#(LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule lpp_answer_transition.probe) (rule probe(4), rule fm, rule fn)
    show ?thesis using probe local gs saved rho
      by (auto simp: lpc_attach_answers_def lpp_probe_goals_def lpp_probe_else_def split: if_splits)
  qed
qed


lemma lpp_attach_barriers_preserved:
  assumes separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and step: "(lpc_attach rest ss,u)\<in>lpp_atomic_source P B U"
  shows "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids u) = {}"
  using step
proof (cases rule: lpp_atomic_source.cases)
  case base
  show ?thesis by (rule lpc_attach_barriers_preserved[OF separated base(2)])
next
  case (probe f ts a keep m gs es n)
  have fm: "lp_cut_fresh m (lpc_attach rest ss)" using probe by simp
  have fn: "lp_cut_fresh n (lpc_attach rest ss)"
    using probe by (auto simp: lp_cut_fresh_def)
  have m: "m\<notin>lpc_rest_scopes rest"
    by (rule lpc_attach_fresh_goals[OF fm]) (use probe in simp)
  have n: "n\<notin>lpc_rest_scopes rest"
    by (rule lpc_attach_fresh_goals[OF fn]) (use probe in simp)
  have before: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (lpc_attach rest ss)) = {}"
    using separated by (simp add: lpc_attach_barriers)
  show ?thesis using before probe m n by simp
qed (use separated in \<open>auto simp: lpc_attach_barriers lpc_barrier_ids_Cons lp_cut_fresh_def lpp_probe_goals_def lpp_probe_else_def split: lp_cut_entry.splits\<close>)

lemma lpp_answer_contract_owned_append:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E (map fst ss)"
    and separated: "E\<inter>set (lpc_barrier_ids (map fst es)) = {}"
    and prefix: "lp_answer_contract (lpp_answer_transition P B U) ss R t ret"
    and suffix: "lp_answer_contract (lpp_answer_transition P B U) es R t ret"
  shows "lp_answer_contract (lpp_answer_transition P B U) (ss@es) R t ret"
proof (rule lp_answer_contract_append[where K = "\<lambda>us. lpc_owned_stack E (map fst us)",
    OF prefix suffix owned])
  show "\<And>us event vs. lpc_owned_stack E (map fst us) \<Longrightarrow>
    lpp_answer_transition P B U us event vs \<Longrightarrow> lpc_owned_stack E (map fst vs)"
    by (rule lpp_owned_answer_preserved[OF program])
  show "\<And>us event result. us\<noteq>[] \<Longrightarrow> lpc_owned_stack E (map fst us) \<Longrightarrow>
    lpp_answer_transition P B U (us@es) event result \<Longrightarrow>
    \<exists>vs. lpp_answer_transition P B U us event vs \<and> (result = vs@es \<or> result = vs)"
    using lpp_owned_answer_append[OF _ _ separated] by blast
qed


end
