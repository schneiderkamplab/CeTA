theory LP_Source_Owned_Delta
 imports LP_Source_Owned_Trace LP_Prolog_NO_Scope_Permutation
begin

text \<open>Only newly allocated scopes must avoid a saved caller stack.
Existing caller scopes may occur in both pending goals and saved alternatives.\<close>

lemma lpc_no_owned_delta_pending:
 assumes step: "(s,t)\<in>lp_cut_mgu_source P"
   and owned: "lpc_no_owned_suffix s"
   and fresh: "((\<Union>e\<in>set t. lp_cut_entry_scopes e) -
     (\<Union>e\<in>set s. lp_cut_entry_scopes e)) \<inter>
     (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
 shows "(s@bs,t@bs)\<in>lp_cut_mgu_source P"

 using step
proof (cases rule: lp_cut_mgu_source.cases)
 case admin
 show ?thesis using lpc_no_owned_admin_pending[OF admin owned]
   by (rule lp_cut_mgu_source.admin)
next
 case (case_call m f ts gs es)
 have fm: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#(es@bs))"
   using case_call fresh by (auto simp: lp_cut_fresh_def)
 show ?thesis using lp_cut_mgu_source.case_call[OF fm, of P]
   by (simp add: case_call append_assoc)
next
 case (resolve c a gs sigma rho m es)
 show ?thesis using resolve by (auto intro: lp_cut_mgu_source.resolve)
next
 case backtrack
 show ?thesis using backtrack by (auto intro: lp_cut_mgu_source.backtrack)
next
 case (unify a b gs sigma es)
 show ?thesis using unify by (auto intro: lp_cut_mgu_source.unify)
next
 case unify_fail
 show ?thesis using unify_fail by (auto intro: lp_cut_mgu_source.unify_fail)
next
 case (meta m a gs es body)
 have fm: "lp_cut_fresh m (LPCGoals (LPCMeta a#gs)#(es@bs))"
   using meta fresh by (auto simp: lp_cut_fresh_def)
 show ?thesis using meta fm by (auto intro: lp_cut_mgu_source.meta)
next
 case meta_unlowerable
 show ?thesis using meta_unlowerable by (auto intro: lp_cut_mgu_source.meta_unlowerable)

qed


lemma lpp_builtin_owned_delta_pending:
  assumes step: "(s,t)\<in>lpp_builtin_source P U"
    and nonempty_target: "t\<noteq>[]"
    and safe: "lpc_no_owned_suffix s"
    and fresh: "((\<Union>e\<in>set t. lp_cut_entry_scopes e) -
       (\<Union>e\<in>set s. lp_cut_entry_scopes e)) \<inter>
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
      by (rule lpc_no_owned_delta_pending[OF ordinary(1) safe fresh])
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



definition lpp_owned_delta_relation where
 "lpp_owned_delta_relation P U S = {(s,t). (s,t)\<in>lpp_builtin_source P U \<and>
   t\<noteq>[] \<and> lpc_no_owned_suffix s \<and>
   ((\<Union>e\<in>set t. lp_cut_entry_scopes e) -
    (\<Union>e\<in>set s. lp_cut_entry_scopes e)) \<subseteq> S}"

lemma lpp_owned_delta_scope_step:
 assumes step: "(s,t)\<in>lpp_owned_delta_relation P U S"
   and injective: "inj r" and program: "lp_cut_source_program P"
   and separated: "r ` S \<inter> (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
 shows "(map (lp_cut_scope_entry r) s @ bs,map (lp_cut_scope_entry r) t @ bs)
   \<in>lpp_builtin_source P U"
proof -
 have actual: "(s,t)\<in>lpp_builtin_source P U"
   and nonempty: "t\<noteq>[]" and owned: "lpc_no_owned_suffix s"
   and support: "((\<Union>e\<in>set t. lp_cut_entry_scopes e) -
    (\<Union>e\<in>set s. lp_cut_entry_scopes e)) \<subseteq> S"
   using step by (auto simp: lpp_owned_delta_relation_def)
 have fresh: "((\<Union>e\<in>set (map (lp_cut_scope_entry r) t). lp_cut_entry_scopes e) -
    (\<Union>e\<in>set (map (lp_cut_scope_entry r) s). lp_cut_entry_scopes e)) \<inter>
    (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
   using support separated by (auto simp: lp_cut_scope_entry_scopes; blast)
 show ?thesis
   by (rule lpp_builtin_owned_delta_pending[OF
     lpp_builtin_source_scope[OF actual injective program] _ _ fresh])
     (use nonempty owned lpc_no_owned_scope_transport[OF injective] in auto)
qed

lemma lpp_owned_delta_scope_trace:
 assumes path: "(s,t)\<in>(lpp_owned_delta_relation P U S)\<^sup>+"
   and injective: "inj r" and program: "lp_cut_source_program P"
   and separated: "r ` S \<inter> (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
 shows "(map (lp_cut_scope_entry r) s @ bs,map (lp_cut_scope_entry r) t @ bs)
   \<in>(lpp_builtin_source P U)\<^sup>+"
 using path
 by (induct rule: trancl_induct)
    (meson lpp_owned_delta_scope_step[OF _ injective program separated]
      r_into_trancl trancl_trans)+

ML \<open>
val checked = [@{thm lpc_no_owned_delta_pending}, @{thm lpp_builtin_owned_delta_pending},
 @{thm lpp_owned_delta_scope_step}, @{thm lpp_owned_delta_scope_trace}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scope-delta suffix transport" else ();
\<close>
end
