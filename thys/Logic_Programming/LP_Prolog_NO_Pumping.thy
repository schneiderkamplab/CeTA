theory LP_Prolog_NO_Pumping
  imports LP_Prolog_Test_NO LP_Cut_NO_Pumping LP_Prolog_Return_Check LP_Source_Barrier_Pumping
begin

abbreviation lpp_builtin_source where
  "lpp_builtin_source P U \<equiv> lp_prolog_source P lpp_builtin_signature
    (lpp_atomic_source P lpp_builtin_signature U)"

lemma lpp_dispatch_append:
  assumes "s\<noteq>[]"
  shows "lpp_builtin_active B (s @ bs)=lpp_builtin_active B s"
    "lpp_undefined P (s @ bs)=lpp_undefined P s"
  using assms by (cases s; auto simp: lpp_builtin_active_def lpp_undefined_def)+

lemma lpp_builtin_source_nonempty:
  "(s,t)\<in>lpp_builtin_source P U \<Longrightarrow> s\<noteq>[]"
  by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def
    elim: lp_cut_mgu_source.cases)

lemma lpp_builtin_source_extend:
  assumes step: "(s,t)\<in>lpp_builtin_source P U"
    and barriers: "lp_cut_barriers bs"
    and fresh: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "\<exists>cs. lp_cut_barriers cs \<and> set cs \<subseteq> set bs \<and>
    (s @ bs,t @ cs)\<in>lpp_builtin_source P U"
proof -
  have nonempty: "s\<noteq>[]" by (rule lpp_builtin_source_nonempty[OF step])
  have gates: "lpp_builtin_active lpp_builtin_signature (s @ bs)=lpp_builtin_active lpp_builtin_signature s"
    "lpp_undefined P (s @ bs)=lpp_undefined P s"
    using lpp_dispatch_append[OF nonempty] by auto
  from step consider
    (ordinary) "(s,t)\<in>lp_cut_mgu_source P" "\<not>lpp_builtin_active lpp_builtin_signature s" "\<not>lpp_undefined P s"
  | (builtin) "(s,t)\<in>lpp_atomic_source P lpp_builtin_signature U" "lpp_builtin_active lpp_builtin_signature s"
  | (error) "lpp_undefined P s" "\<not>lpp_builtin_active lpp_builtin_signature s" "t=[]"
    by (auto simp: lp_prolog_source_def)
  then show ?thesis
  proof cases
    case ordinary
    obtain cs where "lp_cut_barriers cs" "set cs \<subseteq> set bs" "(s @ bs,t @ cs)\<in>lp_cut_mgu_source P"
      using lpc_no_source_extend[OF ordinary(1) barriers fresh] by blast
    then show ?thesis using ordinary gates by (auto simp: lp_prolog_source_def)
  next
    case builtin
    from builtin(1) show ?thesis
    proof (cases rule: lpp_atomic_source.cases)
      case base then show ?thesis using builtin(2) by blast
    next
      case success
      show ?thesis by (rule exI[of _ bs])
        (use success builtin(2) barriers in \<open>auto simp: lp_prolog_source_def lpp_builtin_active_def intro: lpp_atomic_source.success\<close>)
    next
      case failure
      show ?thesis by (rule exI[of _ bs])
        (use failure builtin(2) barriers in \<open>auto simp: lp_prolog_source_def lpp_builtin_active_def intro: lpp_atomic_source.failure\<close>)
    next
      case error
      show ?thesis by (rule exI[of _ "[]"])
        (use error builtin(2) in \<open>auto simp: lp_prolog_source_def lpp_builtin_active_def intro: lpp_atomic_source.error\<close>)
    next
      case (probe f ts a keep m gs es n)
      have fm: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#(es@bs))"
        using probe fresh by (auto simp: lp_cut_fresh_def)
      have fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#(es@bs))"
        using probe fresh by (auto simp: lp_cut_fresh_def)
      have raw: "(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#(es@bs),
        LPCGoals (lpp_probe_goals a keep m gs)#LPCBarrier n#
        LPCGoals (lpp_probe_else keep gs)#LPCBarrier m#(es@bs))
          \<in>lpp_atomic_source P lpp_builtin_signature U"
        by (rule lpp_atomic_source.probe) (rule probe(3), rule fm, rule fn)
      show ?thesis by (rule exI[of _ bs])
        (use raw probe builtin(2) barriers gates in \<open>auto simp: lp_prolog_source_def\<close>)
    qed
  next
    case error
    show ?thesis by (rule exI[of _ "[]"])
      (use error gates in \<open>auto simp: lp_prolog_source_def\<close>)
  qed
qed


lemma lpp_dispatch_scope:
  "lpp_builtin_active B (map (lp_cut_scope_entry r) s)=lpp_builtin_active B s"
  "lpp_undefined P (map (lp_cut_scope_entry r) s)=lpp_undefined P s"
  by (cases s; auto simp: lpp_builtin_active_def lpp_undefined_def lpp_scope_entry_atom)+

lemma lpp_builtin_source_scope:
  assumes step: "(s,t)\<in>lpp_builtin_source P U"
    and injective: "inj r" and program: "lp_cut_source_program P"
  shows "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>lpp_builtin_source P U"
proof -
  from step consider
    (ordinary) "(s,t)\<in>lp_cut_mgu_source P" "\<not>lpp_builtin_active lpp_builtin_signature s" "\<not>lpp_undefined P s"
  | (builtin) "(s,t)\<in>lpp_atomic_source P lpp_builtin_signature U" "lpp_builtin_active lpp_builtin_signature s"
  | (error) "lpp_undefined P s" "\<not>lpp_builtin_active lpp_builtin_signature s" "t=[]"
    by (auto simp: lp_prolog_source_def)
  then show ?thesis
  proof cases
    case ordinary
    show ?thesis using lpc_mgu_scope_source[OF ordinary(1) injective program] ordinary
      by (auto simp: lp_prolog_source_def lpp_dispatch_scope)
  next
    case builtin
    have atomic: "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>lpp_atomic_source P lpp_builtin_signature U"
    proof -
      let ?ss = "map (\<lambda>e. (e,\<lambda>x::string. LPIVar x)) s"
      have original: "(map fst ?ss,t)\<in>lpp_atomic_source P lpp_builtin_signature U"
        using builtin(1) by (simp add: o_def)
      obtain event tt where lifted: "lpp_answer_transition P lpp_builtin_signature U ?ss event tt"
        and erased: "map fst tt=t"
        using lpp_answer_source_lifts[OF original] by blast
      have scoped: "lpp_answer_transition P lpp_builtin_signature U
          (lpc_return_scope r ?ss) event (lpc_return_scope r tt)"
        by (rule lpp_answer_transition_scope[OF lifted injective program])
      show ?thesis using lpp_answer_transition_erases[OF scoped]
        by (simp only: lpc_return_scope_erases erased; simp add: o_def)
    qed
    show ?thesis using atomic builtin(2)
      by (auto simp: lp_prolog_source_def lpp_dispatch_scope)
  next
    case error
    then show ?thesis by (auto simp: lp_prolog_source_def lpp_dispatch_scope)
  qed
qed


lemma lpp_builtin_barrier_execution:
  assumes program: "lp_cut_source_program P"
  shows "lp_barrier_execution (lpp_builtin_source P U)"
proof
  fix s t and r :: "nat \<Rightarrow> nat"
  assume step: "(s,t)\<in>lpp_builtin_source P U" and inj: "inj r"
  show "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>lpp_builtin_source P U"
    by (rule lpp_builtin_source_scope[OF step inj program])
next
  fix s t and bs :: "(string lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assume step: "(s,t)\<in>lpp_builtin_source P U" and bar: "lp_cut_barriers bs"
    and fresh: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter> (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  show "\<exists>cs. lp_cut_barriers cs \<and> set cs \<subseteq> set bs \<and> (s @ bs,t @ cs)\<in>lpp_builtin_source P U"
    by (rule lpp_builtin_source_extend[OF step bar fresh])
qed

end
