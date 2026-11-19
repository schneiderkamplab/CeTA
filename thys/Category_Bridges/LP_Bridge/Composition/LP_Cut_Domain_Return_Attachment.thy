theory LP_Cut_Domain_Return_Attachment
  imports LP_Cut_Domain_Scope_Ownership
begin

context cut_runtime_domain
begin

lemma precise_attach_admin_reflect:
  assumes active: "lpc_prefix_active ss"
    and step: "lp_cut_admin (lpc_attach rest ss) = Some u"
  shows "\<exists>tt. precise_answer_transition P ss None tt \<and> u=lpc_attach rest tt"
proof (cases ss)
  case Nil then show ?thesis using active by simp
next
  case (Cons frame es)
  obtain e \<eta> where frame: "frame=(e,\<eta>)" by (cases frame) auto
  show ?thesis
  proof (cases e)
    case (LPCBarrier m)
    then show ?thesis using step Cons frame
      by (auto intro: precise_answer_transition.barrier)
  next
    case (LPCClause gs c m)
    then show ?thesis using step Cons frame by simp
  next
    case (LPCGoals gs)
    obtain g tail where gs: "gs=g#tail" using active Cons frame LPCGoals by (cases gs) auto
    show ?thesis
    proof (cases g)
      case (LPCCut m)
      have event: "precise_answer_transition P ss None
        ((LPCGoals tail,\<eta>)#lpc_answer_prune m es)"
        using Cons frame LPCGoals gs LPCCut by (simp add: precise_answer_transition.cut)
      show ?thesis using event step Cons frame LPCGoals gs LPCCut
        by (auto simp: lpc_attach_prune)
    qed (use active step Cons frame LPCGoals gs in
      \<open>auto intro: precise_answer_transition.truth precise_answer_transition.failure\<close>)
  qed
qed

theorem precise_attach_active_reflect:
  fixes P :: "('f,string) lp_cut_program"
  assumes active: "lpc_prefix_active ss"
    and step: "(lpc_attach rest ss,u)\<in>precise_source P"
  shows "\<exists>tt. precise_answer_transition P ss None tt \<and> u=lpc_attach rest tt"
proof -
  obtain e \<eta> es where ss: "ss=(e,\<eta>)#es"
    using active by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof cases
    case admin
    show ?thesis by (rule precise_attach_admin_reflect[OF active admin])
  next
    case (case_call m f ts gs tail)
    obtain prefix where shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest"
      and tail: "tail=lpc_attach rest es"
      using case_call active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have fresh: "lp_cut_fresh m (map fst ss)"
      by (rule lpc_attach_fresh[where rest=rest]) (use case_call in simp)
    have event: "precise_answer_transition P ss None
      (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#prefix) c m,\<eta>))
        (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,\<eta>)#es)"
      using fresh by (simp add: ss shape precise_answer_transition.case_call)
    show ?thesis by (rule exI, rule conjI[OF event])
      (use case_call gs tail in \<open>simp add: map_map o_def\<close>)
  next
    case (resolve c a gs \<sigma> \<rho> m tail)
    obtain prefix where shape: "e=LPCClause (LPCAtom a#prefix) c m"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest"
      and tail: "tail=lpc_attach rest es"
      using resolve active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have mgu: "mgu_resolve a prefix (fst (P!c)) (snd (P!c)) \<sigma> \<rho>"
      by (rule precise_resolve_prefix_projection)
        (use resolve gs in simp)
    have event: "precise_answer_transition P ss None
      ((LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) prefix),
        \<lambda>x. lp_isubst (\<eta> x) \<sigma>)#es)"
      unfolding ss shape by (rule precise_answer_transition.resolve) (use resolve mgu in auto)
    show ?thesis by (rule exI, rule conjI[OF event])
      (use resolve gs tail in \<open>simp add: map_map o_def lp_cut_map_comp lp_ieval_subst append_assoc\<close>)
  next
    case (backtrack c a gs m)
    obtain prefix where shape: "e=LPCClause (LPCAtom a#prefix) c m"
      and tail: "u=lpc_attach rest es"
      using backtrack active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have event: "precise_answer_transition P ss None es"
      unfolding ss shape by (rule precise_answer_transition.backtrack) (use backtrack in auto)
    show ?thesis by (rule exI, rule conjI[OF event]) (use backtrack tail in simp)
  next
    case (unify a b gs \<sigma> tail)
    obtain prefix where shape: "e=LPCGoals (LPCUnify a b#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest"
      and tail: "tail=lpc_attach rest es"
      using unify active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have mgu: "mgu_unify a b prefix \<sigma>"
      by (rule precise_unify_prefix_projection) (use unify gs in simp)
    have event: "precise_answer_transition P ss None
      ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) prefix),
        \<lambda>x. lp_isubst (\<eta> x) \<sigma>)#es)"
      unfolding ss shape by (rule precise_answer_transition.unify[OF mgu])
    show ?thesis by (rule exI, rule conjI[OF event])
      (use unify gs tail in \<open>simp add: map_map o_def lp_cut_map_comp lp_ieval_subst\<close>)
  next
    case (unify_fail a b gs)
    obtain prefix where shape: "e=LPCGoals (LPCUnify a b#prefix)"
      and tail: "u=lpc_attach rest es"
      using unify_fail active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have event: "precise_answer_transition P ss None es"
      unfolding ss shape by (rule precise_answer_transition.unify_fail) (use unify_fail in auto)
    show ?thesis by (rule exI, rule conjI[OF event]) (use unify_fail tail in simp)
  next
    case (meta m a gs tail body)
    obtain prefix where shape: "e=LPCGoals (LPCMeta a#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest"
      and tail: "tail=lpc_attach rest es"
      using meta active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have fresh: "lp_cut_fresh m (map fst ss)"
      by (rule lpc_attach_fresh[where rest=rest]) (use meta in simp)
    have event: "precise_answer_transition P ss None
      ((LPCGoals (body@prefix),\<eta>)#(LPCBarrier m,\<eta>)#es)"
      using fresh meta by (auto simp: ss shape intro: precise_answer_transition.meta)
    show ?thesis by (rule exI, rule conjI[OF event]) (use meta gs tail in \<open>simp add: append_assoc\<close>)
  next
    case (meta_unlowerable a gs tail)
    obtain prefix where shape: "e=LPCGoals (LPCMeta a#prefix)"
      using meta_unlowerable active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have event: "precise_answer_transition P ss None ss"
      unfolding ss shape by (rule precise_answer_transition.meta_unlowerable)
        (use meta_unlowerable in auto)
    show ?thesis by (rule exI, rule conjI[OF event]) (use meta_unlowerable in simp)
  qed
qed

end
end
