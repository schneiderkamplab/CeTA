theory LP_Cut_Return_Append
  imports LP_Cut_Return_Source
begin

lemma lpc_answer_prune_append:
  "lpc_answer_prune m (ss@es) =
    (if LPCBarrier m\<in>set (map fst ss) then lpc_answer_prune m ss@es
     else lpc_answer_prune m es)"
  by (induct ss) (auto split: prod.splits lp_cut_entry.splits)

lemma lpc_answer_prune_absent:
  "LPCBarrier m\<notin>set (map fst ss) \<Longrightarrow> lpc_answer_prune m ss=[]"
  by (induct ss) (auto split: prod.splits lp_cut_entry.splits)

lemma lpc_owned_answer_append:
  assumes nonempty: "ss\<noteq>[]"
    and owned: "lpc_owned_stack E (map fst ss)"
    and separated: "E\<inter>set (lpc_barrier_ids (map fst es))={}"
    and step: "lpc_answer_transition P (ss@es) event u"
  shows "\<exists>tt. lpc_answer_transition P ss event tt \<and> (u=tt@es \<or> u=tt)"
proof -
  obtain e eta tail where ss: "ss=(e,eta)#tail"
    using nonempty by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof (cases rule: lpc_answer_transition.cases)
    case (cut m gs rho suffix)
    have shape: "ss=(LPCGoals (LPCCut m#gs),rho)#tail"
      and suffix: "suffix=tail@es" using cut ss by auto
    have external: "m\<in>E \<Longrightarrow> LPCBarrier m\<notin>set (map fst es)"
      using separated by (simp only: lpc_barrier_ids_member[symmetric]) blast
    have member: "m\<in>E \<or> LPCBarrier m\<in>set (map fst tail)"
      using owned by (auto simp: shape lpc_barrier_ids_member)
    have src: "lpc_answer_transition P ss None
      ((LPCGoals gs,rho)#lpc_answer_prune m tail)"
      unfolding shape by (rule lpc_answer_transition.cut)
    show ?thesis
      using cut suffix member external src
      by (auto simp: lpc_answer_prune_append lpc_answer_prune_absent)
  next
    case (case_call m f ts gs suffix rho)
    have shape: "ss=(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),rho)#tail"
      and suffix: "suffix=tail@es" using case_call ss by auto
    have fresh: "lp_cut_fresh m (map fst ss)"
      using case_call shape suffix by (auto simp: lp_cut_fresh_def)
    have src: "lpc_answer_transition P ss None
      (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m,rho))
        (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,rho)#tail)"
      unfolding shape by (rule lpc_answer_transition.case_call) (use fresh shape in simp)
    show ?thesis by (rule exI, rule conjI)
      (use src case_call suffix in \<open>auto simp: append_assoc\<close>)
  next
    case (meta m a gs suffix body rho)
    have shape: "ss=(LPCGoals (LPCMeta a#gs),rho)#tail"
      and suffix: "suffix=tail@es" using meta ss by auto
    have fresh: "lp_cut_fresh m (map fst ss)"
      using meta shape suffix by (auto simp: lp_cut_fresh_def)
    have src: "lpc_answer_transition P ss None
      ((LPCGoals (body@gs),rho)#(LPCBarrier m,rho)#tail)"
      unfolding shape by (rule lpc_answer_transition.meta) (use fresh shape meta in auto)
    show ?thesis by (rule exI, rule conjI)
      (use src meta suffix in auto)
  next
    case (backtrack c a gs m rho)
    have shape: "ss=(LPCClause (LPCAtom a#gs) c m,rho)#tail"
      using backtrack ss by auto
    have src: "lpc_answer_transition P ss None tail"
      unfolding shape by (rule lpc_answer_transition.backtrack) (use backtrack in auto)
    show ?thesis using backtrack ss src by auto
  next
    case (unify_fail a b gs rho)
    have shape: "ss=(LPCGoals (LPCUnify a b#gs),rho)#tail"
      using unify_fail ss by auto
    have src: "lpc_answer_transition P ss None tail"
      unfolding shape by (rule lpc_answer_transition.unify_fail) (use unify_fail in auto)
    show ?thesis using unify_fail ss src by auto
  next
    case (meta_unlowerable a gs rho suffix)
    have shape: "ss=(LPCGoals (LPCMeta a#gs),rho)#tail"
      using meta_unlowerable ss by auto
    have src: "lpc_answer_transition P ss None ss"
      unfolding shape by (rule lpc_answer_transition.meta_unlowerable) (use meta_unlowerable in auto)
    show ?thesis using meta_unlowerable ss src by auto
  qed (use ss in \<open>auto intro: lpc_answer_transition.intros\<close>)
qed

definition lpc_answers_covered where
  "lpc_answers_covered P ss C = (\<forall>us rho vs.
    (ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<longrightarrow>
    lpc_answer_transition P us (Some rho) vs \<longrightarrow> C rho)"

lemma lpc_answers_covered_event:
  "lpc_answers_covered P ss C \<Longrightarrow>
    lpc_answer_transition P ss (Some rho) tt \<Longrightarrow> C rho"
  by (auto simp: lpc_answers_covered_def)

lemma lpc_answers_covered_child:
  assumes covered: "lpc_answers_covered P ss C"
    and step: "lpc_answer_transition P ss event tt"
  shows "lpc_answers_covered P tt C"
proof (unfold lpc_answers_covered_def, intro allI impI)
  fix us rho vs
  assume path: "(tt,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and success: "lpc_answer_transition P us (Some rho) vs"
  have edge: "(ss,tt)\<in>lpc_answer_steps P"
    using step by (auto simp: lpc_answer_steps_def)
  have "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    by (rule converse_rtrancl_into_rtrancl[OF edge path])
  then show "C rho" using covered success by (auto simp: lpc_answers_covered_def)
qed

lemma lpc_answers_covered_intro:
  assumes local: "\<And>event tt. lpc_answer_transition P ss event tt \<Longrightarrow>
    (\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> lpc_answers_covered P tt C"
  shows "lpc_answers_covered P ss C"
proof (unfold lpc_answers_covered_def, intro allI impI)
  fix us rho vs
  assume path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and success: "lpc_answer_transition P us (Some rho) vs"
  from path show "C rho"
  proof (cases rule: converse_rtranclE)
    case base then show ?thesis using local success by blast
  next
    case (step tt)
    obtain event where event: "lpc_answer_transition P ss event tt"
      using step by (auto simp: lpc_answer_steps_def)
    show ?thesis using local[OF event] step success
      by (auto simp: lpc_answers_covered_def)
  qed
qed

theorem lpc_owned_answers_append:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E (map fst ss)"
    and separated: "E\<inter>set (lpc_barrier_ids (map fst es))={}"
    and sn: "SN_on (lpc_answer_steps P) {ss}"
    and prefix: "lpc_answers_covered P ss C"
    and suffix: "lpc_answers_covered P es C"
  shows "lpc_answers_covered P (ss@es) C"
proof -
  have all: "lpc_owned_stack E (map fst us) \<longrightarrow> lpc_answers_covered P us C \<longrightarrow>
      lpc_answers_covered P (us@es) C"
    if finite: "SN_on (lpc_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF finite singletonI], intro impI)
    fix us
    assume ih: "\<And>tt. (us,tt)\<in>lpc_answer_steps P \<Longrightarrow>
      lpc_owned_stack E (map fst tt) \<longrightarrow> lpc_answers_covered P tt C \<longrightarrow>
      lpc_answers_covered P (tt@es) C"
      and owns: "lpc_owned_stack E (map fst us)"
      and coverage: "lpc_answers_covered P us C"
    show "lpc_answers_covered P (us@es) C"
    proof (cases "us=[]")
      case True then show ?thesis using suffix by simp
    next
      case False
      show ?thesis
      proof (rule lpc_answers_covered_intro)
        fix event u assume step: "lpc_answer_transition P (us@es) event u"
        obtain tt where local: "lpc_answer_transition P us event tt"
          and shape: "u=tt@es \<or> u=tt"
          using lpc_owned_answer_append[OF False owns separated step] by blast
        have edge: "(us,tt)\<in>lpc_answer_steps P"
          using local by (auto simp: lpc_answer_steps_def)
        have child_owns: "lpc_owned_stack E (map fst tt)"
          by (rule lpc_owned_source_preserved[OF program owns lpc_answer_transition_erases[OF local]])
        have child: "lpc_answers_covered P tt C"
          by (rule lpc_answers_covered_child[OF coverage local])
        have joined: "lpc_answers_covered P (tt@es) C"
          using ih[OF edge] child_owns child by blast
        show "(\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> lpc_answers_covered P u C"
          using lpc_answers_covered_event[OF coverage] local shape child joined by blast
      qed
    qed
  qed
  show ?thesis using all[OF sn] owned prefix by blast
qed

end
