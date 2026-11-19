theory LP_Cut_Domain_Return_Attached_Answers
  imports LP_Cut_Domain_Return_Append
begin

context cut_runtime_domain
begin

theorem precise_attach_answers_active_reflect:
  fixes P :: "('f,string) lp_cut_program"
  assumes active: "lpc_prefix_active ss"
    and step: "precise_answer_transition P (lpc_attach_answers rest ss) event u"
  shows "event=None \<and> (\<exists>tt. precise_answer_transition P ss None tt \<and>
    u=lpc_attach_answers rest tt)"
proof -
  obtain e eta es where ss: "ss=(e,eta)#es"
    using active by (cases ss; auto split: prod.splits)
  have goals_shape: "\<exists>prefix. e=LPCGoals (g#prefix) \<and>
      gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest \<and>
      tail=lpc_attach_answers rest es \<and> rho=eta"
    if eq: "lpc_attach_answers rest ss=(LPCGoals (g#gs),rho)#tail"
    for g gs rho tail
  proof (cases e)
    case (LPCGoals xs)
    obtain h prefix where xs: "xs=h#prefix"
      using active ss LPCGoals by (cases xs) auto
    show ?thesis using eq by (auto simp: ss LPCGoals xs lpc_attach_answers_def)
  qed (use eq ss in \<open>auto simp: lpc_attach_answers_def\<close>)
  have clause_shape: "\<exists>prefix. e=LPCClause (g#prefix) c m \<and>
      gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest \<and>
      tail=lpc_attach_answers rest es \<and> rho=eta"
    if eq: "lpc_attach_answers rest ss=(LPCClause (g#gs) c m,rho)#tail"
    for g gs c m rho tail
  proof (cases e)
    case (LPCClause xs d n)
    obtain h prefix where xs: "xs=h#prefix"
      using active ss LPCClause by (cases xs) auto
    show ?thesis using eq by (auto simp: ss LPCClause xs lpc_attach_answers_def)
  qed (use eq ss in \<open>auto simp: lpc_attach_answers_def\<close>)
  from step show ?thesis
  proof (cases rule: precise_answer_transition.cases)
    case (barrier m rho)
    have shape: "e=LPCBarrier m"
      using barrier ss by (cases e; auto simp: lpc_attach_answers_def)
    have rho: "rho=eta" and u: "u=lpc_attach_answers rest es"
      using barrier ss shape by (simp_all add: lpc_attach_answers_def)
    have src: "precise_answer_transition P ss None es"
      unfolding ss shape by (rule precise_answer_transition.barrier)
    show ?thesis using barrier src u by auto
  next
    case (success rho)
    then show ?thesis using active ss
      by (cases e; auto simp: lpc_attach_answers_def)
  next
    case (truth gs rho tail)
    obtain prefix where shape: "e=LPCGoals (LPCTrue#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
      and tail: "tail=lpc_attach_answers rest es" and rho: "rho=eta"
      using goals_shape truth by blast
    have src: "precise_answer_transition P ss None ((LPCGoals prefix,eta)#es)"
      unfolding ss shape by (rule precise_answer_transition.truth)
    show ?thesis using truth src gs tail rho
      by (auto simp: lpc_attach_answers_def)
  next
    case (failure gs rho)
    obtain prefix where shape: "e=LPCGoals (LPCFail#prefix)"
      and u: "u=lpc_attach_answers rest es"
      using goals_shape failure by blast
    have src: "precise_answer_transition P ss None es"
      unfolding ss shape by (rule precise_answer_transition.failure)
    show ?thesis using failure src u by auto
  next
    case (cut m gs rho tail)
    obtain prefix where shape: "e=LPCGoals (LPCCut m#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
      and tail: "tail=lpc_attach_answers rest es" and rho: "rho=eta"
      using goals_shape cut by blast
    have src: "precise_answer_transition P ss None ((LPCGoals prefix,eta)#lpc_answer_prune m es)"
      unfolding ss shape by (rule precise_answer_transition.cut)
    have shape_u: "u=lpc_attach_answers rest ((LPCGoals prefix,eta)#lpc_answer_prune m es)"
      using cut gs tail rho lpc_attach_answers_prune[of rest m es]
      by (simp add: lpc_attach_answers_def)
    show ?thesis using cut src shape_u by auto
  next
    case (case_call m f ts gs tail rho)
    obtain prefix where shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
      and tail: "tail=lpc_attach_answers rest es" and rho: "rho=eta"
      using goals_shape case_call by blast
    have fresh: "lp_cut_fresh m (map fst ss)"
      by (rule lpc_attach_fresh[where rest=rest])
        (use case_call in \<open>simp add: lpc_attach_answers_erases[symmetric]\<close>)
    have src: "precise_answer_transition P ss None
      (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#prefix) c m,eta))
        (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule precise_answer_transition.case_call) (use fresh ss shape in simp)
    show ?thesis using case_call src gs tail rho
      by (auto simp: lpc_attach_answers_def map_map o_def)
  next
    case (resolve c a gs sigma nu m rho tail)
    obtain prefix where shape: "e=LPCClause (LPCAtom a#prefix) c m"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
      and tail: "tail=lpc_attach_answers rest es" and rho: "rho=eta"
      using clause_shape resolve by blast
    have mgu: "mgu_resolve a prefix (fst (P!c)) (snd (P!c)) sigma nu"
      by (rule precise_resolve_prefix_projection) (use resolve gs in simp)
    have src: "precise_answer_transition P ss None
      ((LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t nu)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) prefix),
        \<lambda>x. lp_isubst (eta x) sigma)#es)"
      unfolding ss shape by (rule precise_answer_transition.resolve) (use resolve mgu in auto)
    show ?thesis using resolve src gs tail rho
      by (auto simp: lpc_attach_answers_def map_map o_def lp_cut_map_comp lp_ieval_subst append_assoc)
  next
    case (backtrack c a gs m rho)
    obtain prefix where shape: "e=LPCClause (LPCAtom a#prefix) c m"
      and u: "u=lpc_attach_answers rest es"
      using clause_shape backtrack by blast
    have src: "precise_answer_transition P ss None es"
      unfolding ss shape by (rule precise_answer_transition.backtrack) (use backtrack in auto)
    show ?thesis using backtrack src u by auto
  next
    case (unify a b gs sigma rho tail)
    obtain prefix where shape: "e=LPCGoals (LPCUnify a b#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
      and tail: "tail=lpc_attach_answers rest es" and rho: "rho=eta"
      using goals_shape unify by blast
    have mgu: "mgu_unify a b prefix sigma"
      by (rule precise_unify_prefix_projection) (use unify gs in simp)
    have src: "precise_answer_transition P ss None
      ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) prefix),
        \<lambda>x. lp_isubst (eta x) sigma)#es)"
      unfolding ss shape by (rule precise_answer_transition.unify[OF mgu])
    show ?thesis using unify src gs tail rho
      by (auto simp: lpc_attach_answers_def map_map o_def lp_cut_map_comp lp_ieval_subst)
  next
    case (unify_fail a b gs rho)
    obtain prefix where shape: "e=LPCGoals (LPCUnify a b#prefix)"
      and u: "u=lpc_attach_answers rest es"
      using goals_shape unify_fail by blast
    have src: "precise_answer_transition P ss None es"
      unfolding ss shape by (rule precise_answer_transition.unify_fail) (use unify_fail in auto)
    show ?thesis using unify_fail src u by auto
  next
    case (meta m a gs tail body rho)
    obtain prefix where shape: "e=LPCGoals (LPCMeta a#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
      and tail: "tail=lpc_attach_answers rest es" and rho: "rho=eta"
      using goals_shape meta by blast
    have fresh: "lp_cut_fresh m (map fst ss)"
      by (rule lpc_attach_fresh[where rest=rest])
        (use meta in \<open>simp add: lpc_attach_answers_erases[symmetric]\<close>)
    have src: "precise_answer_transition P ss None
      ((LPCGoals (body@prefix),eta)#(LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule precise_answer_transition.meta) (use fresh ss shape meta in auto)
    show ?thesis using meta src gs tail rho
      by (auto simp: lpc_attach_answers_def append_assoc)
  next
    case (meta_unlowerable a gs rho tail)
    obtain prefix where shape: "e=LPCGoals (LPCMeta a#prefix)"
      using goals_shape meta_unlowerable by blast
    have src: "precise_answer_transition P ss None ss"
      unfolding ss shape by (rule precise_answer_transition.meta_unlowerable) (use meta_unlowerable in auto)
    show ?thesis using meta_unlowerable src by auto
  qed
qed

theorem precise_attach_answers_covered:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and contract: "precise_return_contract P ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation_sn: "\<And>eta. (t,ret eta)\<in>R\<^sup>* \<Longrightarrow>
      SN_on (precise_source P) {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest)]}"
    and continuation_answers: "\<And>eta. (t,ret eta)\<in>R\<^sup>* \<Longrightarrow>
      precise_answers_covered P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] C"
  shows "precise_answers_covered P (lpc_attach_answers rest ss) C"
proof -
  let ?E = "lpc_rest_scopes rest"
  have sn: "SN_on (precise_answer_steps P) {ss}"
    using contract precise_answer_instrumentation_SN unfolding precise_return_contract_def by blast
  have all: "(ss,us)\<in>(precise_answer_steps P)\<^sup>* \<longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<longrightarrow>
    ?E\<inter>set (lpc_barrier_ids (map fst us))={} \<longrightarrow>
    precise_answers_covered P (lpc_attach_answers rest us) C"
    if finite: "SN_on (precise_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF finite singletonI], intro impI)
    fix us
    assume ih: "\<And>vs. (us,vs)\<in>precise_answer_steps P \<Longrightarrow>
      (ss,vs)\<in>(precise_answer_steps P)\<^sup>* \<longrightarrow>
      list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs \<longrightarrow>
      ?E\<inter>set (lpc_barrier_ids (map fst vs))={} \<longrightarrow>
      precise_answers_covered P (lpc_attach_answers rest vs) C"
      and path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
      and well: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us"
      and disjoint: "?E\<inter>set (lpc_barrier_ids (map fst us))={}"
    have child: "precise_answers_covered P (lpc_attach_answers rest vs) C"
      if event: "precise_answer_transition P us ev vs"
        and sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}" for ev vs
    proof -
      have edge: "(us,vs)\<in>precise_answer_steps P"
        using event by (auto simp: precise_answer_steps_def)
      have reached: "(ss,vs)\<in>(precise_answer_steps P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF path edge])
      have valid_child: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
        by (rule precise_clause_nonempty_preserved[OF event well])
      show ?thesis using ih[OF edge] reached valid_child sep by blast
    qed
    show "precise_answers_covered P (lpc_attach_answers rest us) C"
    proof (cases "lpc_prefix_active us")
      case True
      show ?thesis
      proof (rule precise_answers_covered_intro)
        fix event u assume step: "precise_answer_transition P (lpc_attach_answers rest us) event u"
        obtain vs where silent: "event=None" and event: "precise_answer_transition P us None vs"
          and shape: "u=lpc_attach_answers rest vs"
          using precise_attach_answers_active_reflect[OF True step] by blast
        have source: "(lpc_attach rest us,lpc_attach rest vs)\<in>precise_source P"
          using precise_answer_transition_erases[OF step] by (simp add: shape lpc_attach_answers_erases)
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}"
          using precise_attach_barriers_preserved[OF disjoint source] by (simp add: lpc_attach_barriers)
        show "(\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> precise_answers_covered P u C"
          using child[OF event sep] by (simp add: shape silent)
      qed
    next
      case False
      show ?thesis
      proof (cases us)
        case Nil
        show ?thesis unfolding Nil lpc_attach_answers_def
          by (rule precise_answers_covered_intro) (auto elim: precise_answer_transition.cases)
      next
        case (Cons frame vs)
        obtain e eta where frame: "frame=(e,eta)" by (cases frame) auto
        have e: "e=LPCGoals []" using False well Cons frame by (cases e) auto
        have event: "precise_answer_transition P us (Some eta) vs"
          by (simp add: Cons frame e precise_answer_transition.success)
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}"
          using disjoint by (simp add: Cons frame e)
        have tail: "precise_answers_covered P (lpc_attach_answers rest vs) C"
          by (rule child[OF event sep])
        let ?gs = "map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest"
        have reached: "(t,ret eta)\<in>R\<^sup>*"
          using contract path event unfolding precise_return_contract_def by blast
        have first_sn: "SN_on (precise_answer_steps P) {[(LPCGoals ?gs,eta)]}"
          using continuation_sn[OF reached] by (simp add: precise_answer_instrumentation_SN)
        have first: "precise_answers_covered P [(LPCGoals ?gs,eta)] C"
          by (rule continuation_answers[OF reached])
        have owns: "lpc_owned_stack ?E (map fst [(LPCGoals ?gs,eta)])"
          using lpc_owned_external_goals[of rest ?E "[]"] by (simp add: lpc_owned_goals_map)
        have separated_tail: "?E\<inter>set (lpc_barrier_ids (map fst (lpc_attach_answers rest vs)))={}"
          using sep by (simp add: lpc_attach_answers_erases lpc_attach_barriers)
        have joined: "precise_answers_covered P ([(LPCGoals ?gs,eta)] @ lpc_attach_answers rest vs) C"
          by (rule precise_owned_answers_append[OF program owns separated_tail first_sn first tail])
        show ?thesis using joined by (simp add: Cons frame e lpc_attach_answers_def)
      qed
    qed
  qed
  show ?thesis using all[OF sn] valid separated by simp
qed

theorem precise_return_contract_compose:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and prefix: "precise_return_contract P ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. (t,ret eta)\<in>R\<^sup>* \<Longrightarrow>
      precise_return_contract P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
  shows "precise_return_contract P (lpc_attach_answers rest ss) R t final"
proof -
  have continuation_sn: "SN_on (precise_source P)
      {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest)]}"
    if "(t,ret eta)\<in>R\<^sup>*" for eta
    using continuation[OF that] by (simp add: precise_return_contract_def)
  have source: "SN_on (precise_source P) {lpc_attach rest ss}"
    by (rule precise_return_source_SN[OF program prefix valid separated continuation_sn])
  have answers: "precise_answers_covered P (lpc_attach_answers rest ss) (\<lambda>rho. (t,final rho)\<in>R\<^sup>*)"
  proof (rule precise_attach_answers_covered[OF program prefix valid separated continuation_sn])
    fix eta assume reached: "(t,ret eta)\<in>R\<^sup>*"
    show "precise_answers_covered P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)]
      (\<lambda>rho. (t,final rho)\<in>R\<^sup>*)"
    proof (unfold precise_answers_covered_def, intro allI impI)
      fix us rho vs
      assume path: "([(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)],us)
          \<in>(precise_answer_steps P)\<^sup>*"
        and event: "precise_answer_transition P us (Some rho) vs"
      have tail: "(ret eta,final rho)\<in>R\<^sup>*"
        using continuation[OF reached] path event unfolding precise_return_contract_def by blast
      show "(t,final rho)\<in>R\<^sup>*" by (rule rtrancl_trans[OF reached tail])
    qed
  qed
  show ?thesis using source answers
    by (auto simp: precise_return_contract_def precise_answers_covered_def lpc_attach_answers_erases)
qed

end
end
