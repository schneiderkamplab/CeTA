theory LP_Cut_Domain_Return_Append
  imports LP_Cut_Domain_Return_Source
begin

context cut_runtime_domain
begin

lemma precise_owned_answer_append:
  assumes nonempty: "ss\<noteq>[]"
    and owned: "lpc_owned_stack E (map fst ss)"
    and separated: "E\<inter>set (lpc_barrier_ids (map fst es))={}"
    and step: "precise_answer_transition P (ss@es) event u"
  shows "\<exists>tt. precise_answer_transition P ss event tt \<and> (u=tt@es \<or> u=tt)"
proof -
  obtain e eta tail where ss: "ss=(e,eta)#tail"
    using nonempty by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof (cases rule: precise_answer_transition.cases)
    case (cut m gs rho suffix)
    have shape: "ss=(LPCGoals (LPCCut m#gs),rho)#tail"
      and suffix: "suffix=tail@es" using cut ss by auto
    have external: "m\<in>E \<Longrightarrow> LPCBarrier m\<notin>set (map fst es)"
      using separated by (simp only: lpc_barrier_ids_member[symmetric]) blast
    have member: "m\<in>E \<or> LPCBarrier m\<in>set (map fst tail)"
      using owned by (auto simp: shape lpc_barrier_ids_member)
    have src: "precise_answer_transition P ss None
      ((LPCGoals gs,rho)#lpc_answer_prune m tail)"
      unfolding shape by (rule precise_answer_transition.cut)
    show ?thesis
      using cut suffix member external src
      by (auto simp: lpc_answer_prune_append lpc_answer_prune_absent)
  next
    case (case_call m f ts gs suffix rho)
    have shape: "ss=(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),rho)#tail"
      and suffix: "suffix=tail@es" using case_call ss by auto
    have fresh: "lp_cut_fresh m (map fst ss)"
      using case_call shape suffix by (auto simp: lp_cut_fresh_def)
    have src: "precise_answer_transition P ss None
      (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m,rho))
        (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,rho)#tail)"
      unfolding shape by (rule precise_answer_transition.case_call) (use fresh shape in simp)
    show ?thesis by (rule exI, rule conjI)
      (use src case_call suffix in \<open>auto simp: append_assoc\<close>)
  next
    case (meta m a gs suffix body rho)
    have shape: "ss=(LPCGoals (LPCMeta a#gs),rho)#tail"
      and suffix: "suffix=tail@es" using meta ss by auto
    have fresh: "lp_cut_fresh m (map fst ss)"
      using meta shape suffix by (auto simp: lp_cut_fresh_def)
    have src: "precise_answer_transition P ss None
      ((LPCGoals (body@gs),rho)#(LPCBarrier m,rho)#tail)"
      unfolding shape by (rule precise_answer_transition.meta) (use fresh shape meta in auto)
    show ?thesis by (rule exI, rule conjI)
      (use src meta suffix in auto)
  next
    case (backtrack c a gs m rho)
    have shape: "ss=(LPCClause (LPCAtom a#gs) c m,rho)#tail"
      using backtrack ss by auto
    have src: "precise_answer_transition P ss None tail"
      unfolding shape by (rule precise_answer_transition.backtrack) (use backtrack in auto)
    show ?thesis using backtrack ss src by auto
  next
    case (unify_fail a b gs rho)
    have shape: "ss=(LPCGoals (LPCUnify a b#gs),rho)#tail"
      using unify_fail ss by auto
    have src: "precise_answer_transition P ss None tail"
      unfolding shape by (rule precise_answer_transition.unify_fail) (use unify_fail in auto)
    show ?thesis using unify_fail ss src by auto
  next
    case (meta_unlowerable a gs rho suffix)
    have shape: "ss=(LPCGoals (LPCMeta a#gs),rho)#tail"
      using meta_unlowerable ss by auto
    have src: "precise_answer_transition P ss None ss"
      unfolding shape by (rule precise_answer_transition.meta_unlowerable) (use meta_unlowerable in auto)
    show ?thesis using meta_unlowerable ss src by auto
  qed (use ss in \<open>auto intro: precise_answer_transition.intros\<close>)
qed

theorem precise_owned_answers_append:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E (map fst ss)"
    and separated: "E\<inter>set (lpc_barrier_ids (map fst es))={}"
    and sn: "SN_on (precise_answer_steps P) {ss}"
    and prefix: "precise_answers_covered P ss C"
    and suffix: "precise_answers_covered P es C"
  shows "precise_answers_covered P (ss@es) C"
proof -
  have all: "lpc_owned_stack E (map fst us) \<longrightarrow> precise_answers_covered P us C \<longrightarrow>
      precise_answers_covered P (us@es) C"
    if finite: "SN_on (precise_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF finite singletonI], intro impI)
    fix us
    assume ih: "\<And>tt. (us,tt)\<in>precise_answer_steps P \<Longrightarrow>
      lpc_owned_stack E (map fst tt) \<longrightarrow> precise_answers_covered P tt C \<longrightarrow>
      precise_answers_covered P (tt@es) C"
      and owns: "lpc_owned_stack E (map fst us)"
      and coverage: "precise_answers_covered P us C"
    show "precise_answers_covered P (us@es) C"
    proof (cases "us=[]")
      case True then show ?thesis using suffix by simp
    next
      case False
      show ?thesis
      proof (rule precise_answers_covered_intro)
        fix event u assume step: "precise_answer_transition P (us@es) event u"
        obtain tt where local: "precise_answer_transition P us event tt"
          and shape: "u=tt@es \<or> u=tt"
          using precise_owned_answer_append[OF False owns separated step] by blast
        have edge: "(us,tt)\<in>precise_answer_steps P"
          using local by (auto simp: precise_answer_steps_def)
        have child_owns: "lpc_owned_stack E (map fst tt)"
          by (rule precise_owned_source_preserved[OF program owns precise_answer_transition_erases[OF local]])
        have child: "precise_answers_covered P tt C"
          by (rule precise_answers_covered_child[OF coverage local])
        have joined: "precise_answers_covered P (tt@es) C"
          using ih[OF edge] child_owns child by blast
        show "(\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> precise_answers_covered P u C"
          using precise_answers_covered_event[OF coverage] local shape child joined by blast
      qed
    qed
  qed
  show ?thesis using all[OF sn] owned prefix by blast
qed

end
end
