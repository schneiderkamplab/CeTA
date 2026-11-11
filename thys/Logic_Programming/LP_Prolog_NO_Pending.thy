theory LP_Prolog_NO_Pending
 imports LP_Prolog_NO_Pumping LP_Source_Pending_Pumping
begin

lemma lpp_builtin_source_pending:
  assumes step: "(s,t)\<in>lpp_builtin_source P U"
    and nonempty_target: "t\<noteq>[]"
    and safe: "lpc_no_suffix_safe s"
    and fresh: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "(s @ bs,t @ bs)\<in>lpp_builtin_source P U"
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
    have "(s @ bs,t @ bs)\<in>lp_cut_mgu_source P"
      by (rule lpc_no_source_pending[OF ordinary(1) safe fresh])
    then show ?thesis using ordinary gates by (auto simp: lp_prolog_source_def)
  next
    case builtin
    from builtin(1) show ?thesis
    proof (cases rule: lpp_atomic_source.cases)
      case base then show ?thesis using builtin(2) by blast
    next
      case success
      show ?thesis
        by (use success builtin(2) in \<open>auto simp: lp_prolog_source_def lpp_builtin_active_def intro: lpp_atomic_source.success\<close>)
    next
      case failure
      show ?thesis
        by (use failure builtin(2) in \<open>auto simp: lp_prolog_source_def lpp_builtin_active_def intro: lpp_atomic_source.failure\<close>)
    next
      case error
      show ?thesis using error nonempty_target by simp
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
      show ?thesis
        by (use raw probe builtin(2) gates in \<open>auto simp: lp_prolog_source_def\<close>)
    next
      case (branch f ts cond yes no m gs es n)
      have fm: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#(es@bs))"
        using branch fresh by (auto simp: lp_cut_fresh_def)
      have fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#(es@bs))"
        using branch fresh by (auto simp: lp_cut_fresh_def)
      have raw: "(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#(es@bs),
        LPCGoals (cond@(LPCCut m#(yes@gs)))#LPCBarrier n#
        LPCGoals (no@gs)#LPCBarrier m#(es@bs))
          \<in>lpp_atomic_source P lpp_builtin_signature U"
        by (rule lpp_atomic_source.branch) (rule branch(3), rule branch(4), rule fm, rule fn)
      show ?thesis
        by (use raw branch builtin(2) gates in \<open>auto simp: lp_prolog_source_def\<close>)
    next
      case call
      show ?thesis
        by (use call builtin(2) in \<open>auto simp: lp_prolog_source_def lpp_builtin_active_def intro: lpp_atomic_source.call\<close>)
    next
      case choice
      show ?thesis
        by (use choice builtin(2) in \<open>auto simp: lp_prolog_source_def lpp_builtin_active_def intro!: lpp_atomic_source.choice\<close>)
    qed
  next
    case error
    show ?thesis using error nonempty_target by simp
  qed
qed

lemma lpp_builtin_pending_execution:
 assumes "lp_cut_source_program P"
 shows "lp_pending_execution (lpp_builtin_source P U)"
 by (rule lp_pending_execution.intro[OF lpp_builtin_barrier_execution[OF assms]])
   (unfold_locales; rule lpp_builtin_source_pending; assumption)

ML \<open>
val checked = [@{thm lp_pending_execution.pending_pump}, @{thm lpp_builtin_pending_execution}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted pending-stack source pump" else ();
\<close>
end
