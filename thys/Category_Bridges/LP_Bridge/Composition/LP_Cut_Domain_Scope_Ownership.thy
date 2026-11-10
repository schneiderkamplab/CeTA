theory LP_Cut_Domain_Scope_Ownership
  imports Category_LP_Cut_Return_Bridge.LP_Cut_Domain_Return_Module_Triples Category_LP_Cut_Return_Bridge.LP_Cut_Domain_Return_Sequence
begin

context cut_runtime_domain
begin

theorem precise_owned_source_preserved:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E ss"
    and step: "(ss,tt)\<in>precise_source P"
  shows "lpc_owned_stack E tt"
  using step
proof (cases rule: precise_source.cases)
  case admin
  then show ?thesis using owned by (auto intro: lpc_owned_admin)
next
  case (case_call m f ts gs es)
  have fresh: "m\<notin>\<Union>(lp_cut_goal_scopes ` set (LPCAtom (LPIFun (LPCUser f) ts)#gs))"
    using case_call by (auto simp: lp_cut_fresh_def)
  show ?thesis using owned case_call lpc_owned_case_stack[OF fresh, of E es]
    by simp
next
  case (resolve c a gs \<sigma> \<rho> m es)
  have body: "list_all lp_cut_source_goal (snd (P!c))"
    using program resolve by (auto simp: lp_cut_source_program_def)
  have goals: "lpc_owned_goals E (lpc_barrier_ids es)
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)"
    by (rule lpc_owned_bound_body[OF body])
      (use resolve owned in \<open>auto simp: lpc_owned_goals_map\<close>)
  show ?thesis using resolve owned goals by simp
next
  case (meta m a gs es body)
  have fresh: "m\<notin>\<Union>(lp_cut_goal_scopes ` set gs)"
    using meta by (auto simp: lp_cut_fresh_def)
  have tail: "lpc_owned_goals E (m#lpc_barrier_ids es) gs"
    using meta owned by (simp add: lpc_owned_fresh_barrier[OF fresh])
  have goals: "lpc_owned_goals E (m#lpc_barrier_ids es) (body@gs)"
    by (rule lpc_owned_lower) (use meta tail in auto)
  show ?thesis using meta owned goals by simp
qed (use owned in \<open>auto simp: lpc_owned_goals_map\<close>)

lemma precise_owned_source_append:
  assumes nonempty: "ss\<noteq>[]" and owned: "lpc_owned_stack E ss"
    and separated: "E\<inter>set (lpc_barrier_ids es) = {}"
    and step: "(ss@es,u)\<in>precise_source P"
  shows "\<exists>tt. (ss,tt)\<in>precise_source P \<and> (u=tt@es \<or> u=tt)"
proof -
  obtain e tail where ss: "ss=e#tail" using nonempty by (cases ss) auto
  from step show ?thesis
  proof cases
    case admin
    then show ?thesis using lpc_owned_admin_append[OF nonempty owned separated]
      by (blast intro: precise_source.admin)
  next
    case (case_call m f ts gs suffix)
    have shape: "ss=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#tail"
      and suffix: "suffix=tail@es" using case_call ss by auto
    have fresh: "lp_cut_fresh m ss" using case_call shape suffix
      by (auto simp: lp_cut_fresh_def)
    have src: "(ss,map (\<lambda>c. LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m)
      (lp_cut_slice P (LPCUser f) (length ts)) @ LPCBarrier m#tail)\<in>precise_source P"
      unfolding shape by (rule precise_source.case_call) (use fresh shape in simp)
    show ?thesis by (rule exI, rule conjI[OF src])
      (use case_call suffix in \<open>simp add: append_assoc\<close>)
  next
    case (resolve c a gs \<sigma> \<rho> m suffix)
    have shape: "ss=LPCClause (LPCAtom a#gs) c m#tail"
      and suffix: "suffix=tail@es" using resolve ss by auto
    have src: "(ss,LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)#tail)\<in>precise_source P"
      unfolding shape by (rule precise_source.resolve) (use resolve in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (use resolve suffix in simp)
  next
    case (backtrack c a gs m)
    have shape: "ss=LPCClause (LPCAtom a#gs) c m#tail"
      and u: "u=tail@es" using backtrack ss by auto
    have src: "(ss,tail)\<in>precise_source P"
      unfolding shape by (rule precise_source.backtrack) (use backtrack in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (simp add: u)
  next
    case (unify a b gs \<sigma> suffix)
    have shape: "ss=LPCGoals (LPCUnify a b#gs)#tail"
      and suffix: "suffix=tail@es" using unify ss by auto
    have src: "(ss,LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)#tail)
        \<in>precise_source P"
      unfolding shape by (rule precise_source.unify) (use unify in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (use unify suffix in simp)
  next
    case (unify_fail a b gs)
    have shape: "ss=LPCGoals (LPCUnify a b#gs)#tail"
      and u: "u=tail@es" using unify_fail ss by auto
    have src: "(ss,tail)\<in>precise_source P"
      unfolding shape by (rule precise_source.unify_fail) (use unify_fail in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (simp add: u)
  next
    case (meta m a gs suffix body)
    have shape: "ss=LPCGoals (LPCMeta a#gs)#tail"
      and suffix: "suffix=tail@es" using meta ss by auto
    have fresh: "lp_cut_fresh m ss" using meta shape suffix
      by (auto simp: lp_cut_fresh_def)
    have src: "(ss,LPCGoals (body@gs)#LPCBarrier m#tail)\<in>precise_source P"
      unfolding shape by (rule precise_source.meta) (use meta fresh shape in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (use meta suffix in simp)
  next
    case (meta_unlowerable a gs suffix)
    have shape: "ss=LPCGoals (LPCMeta a#gs)#tail"
      and suffix: "suffix=tail@es" using meta_unlowerable ss by auto
    have src: "(ss,ss)\<in>precise_source P"
      unfolding shape by (rule precise_source.meta_unlowerable) (use meta_unlowerable in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (use meta_unlowerable suffix shape in simp)
  qed
qed

theorem precise_owned_append_SN:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E ss"
    and separated: "E\<inter>set (lpc_barrier_ids es) = {}"
    and first: "SN_on (precise_source P) {ss}"
    and later: "SN_on (precise_source P) {es}"
  shows "SN_on (precise_source P) {ss@es}"
proof -
  have all: "SN_on (precise_source P) {ss} \<and>
    (lpc_owned_stack E ss \<longrightarrow> SN_on (precise_source P) {ss@es})"
  proof (rule SN_on_induct[OF first singletonI])
    fix ss
    assume ih: "\<And>tt. (ss,tt)\<in>precise_source P \<Longrightarrow>
      SN_on (precise_source P) {tt} \<and>
      (lpc_owned_stack E tt \<longrightarrow> SN_on (precise_source P) {tt@es})"
    show "SN_on (precise_source P) {ss} \<and>
      (lpc_owned_stack E ss \<longrightarrow> SN_on (precise_source P) {ss@es})"
    proof (intro conjI impI)
      show "SN_on (precise_source P) {ss}"
        by (rule step_reflects_SN_on) (use ih in blast)
    next
      assume own: "lpc_owned_stack E ss"
      show "SN_on (precise_source P) {ss@es}"
      proof (cases "ss=[]")
        case True then show ?thesis using later by simp
      next
        case False
        show ?thesis
        proof (rule step_reflects_SN_on)
          fix u assume st: "(ss@es,u)\<in>precise_source P"
          obtain tt where src: "(ss,tt)\<in>precise_source P"
            and shape: "u=tt@es \<or> u=tt"
            using precise_owned_source_append[OF False own separated st] by blast
          have child_owned: "lpc_owned_stack E tt"
            by (rule precise_owned_source_preserved[OF program own src])
          show "SN_on (precise_source P) {u}"
            using ih[OF src] child_owned shape by blast
        qed
      qed
    qed
  qed
  show ?thesis using all owned by blast
qed

end
end
