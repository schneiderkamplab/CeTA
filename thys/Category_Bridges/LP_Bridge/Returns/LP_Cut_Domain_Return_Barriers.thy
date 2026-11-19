theory LP_Cut_Domain_Return_Barriers
  imports LP_Cut_Domain_Return_Coverage
begin

context cut_runtime_domain
begin

lemma precise_answer_append_suffix:
  assumes nonempty: "ss\<noteq>[]"
    and step: "precise_answer_transition P (ss@es) event u"
  shows "\<exists>tt n. precise_answer_transition P ss event tt \<and> u=tt@drop n es"
proof -
  obtain e eta tail where ss: "ss=(e,eta)#tail"
    using nonempty by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof (cases rule: precise_answer_transition.cases)
    case (cut m gs rho suffix)
    have shape: "ss=(LPCGoals (LPCCut m#gs),rho)#tail"
      and suffix: "suffix=tail@es" using cut ss by auto
    have src: "precise_answer_transition P ss None ((LPCGoals gs,rho)#lpc_answer_prune m tail)"
      unfolding shape by (rule precise_answer_transition.cut)
    obtain n where n: "lpc_answer_prune m es=drop n es" using lpc_answer_prune_suffix by blast
    show ?thesis
    proof (cases "LPCBarrier m\<in>set (map fst tail)")
      case True
      show ?thesis by (rule exI, rule exI[of _ 0], rule conjI)
        (use src cut suffix True in \<open>auto simp: lpc_answer_prune_append\<close>)
    next
      case False
      show ?thesis by (rule exI, rule exI[of _ n], rule conjI)
        (use src cut suffix False n in \<open>auto simp: lpc_answer_prune_append lpc_answer_prune_absent\<close>)
    qed
  next
    case (case_call m f ts gs suffix rho)
    have shape: "ss=(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),rho)#tail"
      and suffix: "suffix=tail@es" using case_call ss by auto
    have fresh: "lp_cut_fresh m (map fst ss)" using case_call shape suffix by (auto simp: lp_cut_fresh_def)
    have src: "precise_answer_transition P ss None
      (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m,rho))
        (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,rho)#tail)"
      unfolding shape by (rule precise_answer_transition.case_call) (use fresh shape in simp)
    show ?thesis by (rule exI, rule exI[of _ 0], rule conjI)
      (use src case_call suffix in \<open>auto simp: append_assoc\<close>)
  next
    case (meta m a gs suffix body rho)
    have shape: "ss=(LPCGoals (LPCMeta a#gs),rho)#tail"
      and suffix: "suffix=tail@es" using meta ss by auto
    have fresh: "lp_cut_fresh m (map fst ss)" using meta shape suffix by (auto simp: lp_cut_fresh_def)
    have src: "precise_answer_transition P ss None ((LPCGoals (body@gs),rho)#(LPCBarrier m,rho)#tail)"
      unfolding shape by (rule precise_answer_transition.meta) (use fresh shape meta in auto)
    show ?thesis by (rule exI, rule exI[of _ 0], rule conjI) (use src meta suffix in auto)
  next
    case (backtrack c a gs m rho)
    have shape: "ss=(LPCClause (LPCAtom a#gs) c m,rho)#tail" using backtrack ss by auto
    have src: "precise_answer_transition P ss None tail"
      unfolding shape by (rule precise_answer_transition.backtrack) (use backtrack in auto)
    show ?thesis by (rule exI, rule exI[of _ 0], rule conjI) (use backtrack ss src in auto)
  next
    case (unify_fail a b gs rho)
    have shape: "ss=(LPCGoals (LPCUnify a b#gs),rho)#tail" using unify_fail ss by auto
    have src: "precise_answer_transition P ss None tail"
      unfolding shape by (rule precise_answer_transition.unify_fail) (use unify_fail in auto)
    show ?thesis by (rule exI, rule exI[of _ 0], rule conjI) (use unify_fail ss src in auto)
  next
    case (meta_unlowerable a gs rho suffix)
    have shape: "ss=(LPCGoals (LPCMeta a#gs),rho)#tail" using meta_unlowerable ss by auto
    have src: "precise_answer_transition P ss None ss"
      unfolding shape by (rule precise_answer_transition.meta_unlowerable) (use meta_unlowerable in auto)
    show ?thesis by (rule exI, rule exI[of _ 0], rule conjI) (use meta_unlowerable ss src in auto)
  qed (use ss in \<open>force intro: exI[of _ 0] precise_answer_transition.intros\<close>)+
qed

lemma precise_answer_barriers_covered:
  "lp_cut_barriers (map fst bs) \<Longrightarrow> precise_answers_covered P bs C"
proof (induct bs)
  case Nil show ?case by (rule precise_answers_covered_intro) (auto elim: precise_answer_transition.cases)
next
  case (Cons frame bs)
  obtain m eta where frame: "frame=(LPCBarrier m,eta)"
    using Cons.prems by (cases frame; cases "fst frame"; auto)
  have tail: "precise_answers_covered P bs C" using Cons by (simp add: frame)
  show ?case by (rule precise_answers_covered_intro)
    (use tail in \<open>auto simp: frame elim: precise_answer_transition.cases\<close>)
qed

lemma precise_answer_append_barriers_covered:
  fixes P :: "('f,string) lp_cut_program"
    and ss bs :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
  assumes sn: "SN_on (precise_answer_steps P) {ss}"
    and coverage: "precise_answers_covered P ss C"
    and barriers: "lp_cut_barriers (map fst bs)"
  shows "precise_answers_covered P (ss@bs) C"
proof -
  have all: "precise_answers_covered P us C \<longrightarrow>
      (\<forall>bs. lp_cut_barriers (map fst bs) \<longrightarrow> precise_answers_covered P (us@bs) C)"
    if finite: "SN_on (precise_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF finite singletonI], intro impI allI)
    fix us bs :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
    assume ih: "\<And>vs. (us,vs)\<in>precise_answer_steps P \<Longrightarrow>
      precise_answers_covered P vs C \<longrightarrow>
      (\<forall>cs. lp_cut_barriers (map fst cs) \<longrightarrow> precise_answers_covered P (vs@cs) C)"
      and covered: "precise_answers_covered P us C"
      and bs: "lp_cut_barriers (map fst bs)"
    show "precise_answers_covered P (us@bs) C"
    proof (cases "us=[]")
      case True
      show ?thesis using precise_answer_barriers_covered[OF bs, of P C] by (simp add: True)
    next
      case False
      show ?thesis
      proof (rule precise_answers_covered_intro)
        fix event result assume step: "precise_answer_transition P (us@bs) event result"
        obtain vs n where local: "precise_answer_transition P us event vs"
          and shape: "result=vs@drop n bs" using precise_answer_append_suffix[OF False step] by blast
        have edge: "(us,vs)\<in>precise_answer_steps P" using local by (auto simp: precise_answer_steps_def)
        have child: "precise_answers_covered P vs C" by (rule precise_answers_covered_child[OF covered local])
        have tail: "lp_cut_barriers (map fst (drop n bs))"
          using bs by (auto simp: list_all_iff dest: in_set_dropD)
        have joined: "precise_answers_covered P (vs@drop n bs) C" using ih[OF edge] child tail by blast
        show "(\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> precise_answers_covered P result C"
          using precise_answers_covered_event[OF covered] local joined shape by blast
      qed
    qed
  qed
  show ?thesis using all[OF sn] coverage barriers by blast
qed

theorem precise_return_contract_append_barriers:
  assumes contract: "precise_return_contract P ss R t ret"
    and barriers: "lp_cut_barriers (map fst bs)"
  shows "precise_return_contract P (ss@bs) R t ret"
proof -
  have sn: "SN_on (precise_source P) {map fst ss}"
    and covered: "precise_answers_covered P ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
    using contract by (auto simp: precise_return_contract_def precise_answers_covered_def)
  have source: "SN_on (precise_source P) {map fst (ss@bs)}"
    using precise_append_barriers_SN[OF sn barriers] by simp
  have outputs: "precise_answers_covered P (ss@bs) (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
    by (rule precise_answer_append_barriers_covered[OF _ covered barriers])
      (use sn in \<open>simp add: precise_answer_instrumentation_SN\<close>)
  show ?thesis using source outputs by (auto simp: precise_return_contract_def precise_answers_covered_def)
qed


end
end
