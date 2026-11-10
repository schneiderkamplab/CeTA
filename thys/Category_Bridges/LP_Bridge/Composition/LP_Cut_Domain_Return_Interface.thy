theory LP_Cut_Domain_Return_Interface
  imports LP_Cut_Domain_Return_Actual
begin

context cut_runtime_domain
begin

lemma precise_reinterface_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "precise_answer_transition P (lpc_reinterface F ss) event tt"
  shows "\<exists>ev us. precise_answer_transition P ss ev us \<and>
    map_option F ev=event \<and> lpc_reinterface F us=tt"
proof -
  have nonempty: "ss\<noteq>[]" using step
    by (auto simp: lpc_reinterface_def elim: precise_answer_transition.cases)
  obtain e eta es where ss: "ss=(e,eta)#es" using nonempty by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof (cases rule: precise_answer_transition.cases)
    case (cut m gs rho suffix)
    have shape: "e=LPCGoals (LPCCut m#gs)" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using cut ss by (auto simp: lpc_reinterface_def)
    have src: "precise_answer_transition P ss None ((LPCGoals gs,eta)#lpc_answer_prune m es)"
      unfolding ss shape by (rule precise_answer_transition.cut)
    show ?thesis using cut src rho suffix lpc_reinterface_prune[of F m es]
      by (auto simp: lpc_reinterface_def)
  next
    case (case_call m f ts gs suffix rho)
    have shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using case_call ss by (auto simp: lpc_reinterface_def)
    have fresh: "lp_cut_fresh m (map fst ss)"
      using case_call by (simp add: ss shape suffix)
    have src: "precise_answer_transition P ss None
      (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m,eta))
        (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule precise_answer_transition.case_call) (use fresh ss shape in simp)
    show ?thesis using case_call src rho suffix
      by (auto simp: lpc_reinterface_def map_map o_def)
  next
    case (resolve c a gs sigma nu m rho suffix)
    have shape: "e=LPCClause (LPCAtom a#gs) c m" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using resolve ss by (auto simp: lpc_reinterface_def)
    have src: "precise_answer_transition P ss None
      ((LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t nu)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),\<lambda>x. lp_isubst (eta x) sigma)#es)"
      unfolding ss shape by (rule precise_answer_transition.resolve) (use resolve in auto)
    show ?thesis using resolve src rho suffix
      by (auto simp: lpc_reinterface_def commute)
  next
    case (backtrack c a gs m rho)
    have shape: "e=LPCClause (LPCAtom a#gs) c m" and tail: "tt=lpc_reinterface F es"
      using backtrack ss by (auto simp: lpc_reinterface_def)
    have src: "precise_answer_transition P ss None es"
      unfolding ss shape by (rule precise_answer_transition.backtrack) (use backtrack in auto)
    show ?thesis using backtrack src tail by auto
  next
    case (unify a b gs sigma rho suffix)
    have shape: "e=LPCGoals (LPCUnify a b#gs)" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using unify ss by (auto simp: lpc_reinterface_def)
    have src: "precise_answer_transition P ss None
      ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),\<lambda>x. lp_isubst (eta x) sigma)#es)"
      unfolding ss shape by (rule precise_answer_transition.unify) (use unify in auto)
    show ?thesis using unify src rho suffix by (auto simp: lpc_reinterface_def commute)
  next
    case (unify_fail a b gs rho)
    have shape: "e=LPCGoals (LPCUnify a b#gs)" and tail: "tt=lpc_reinterface F es"
      using unify_fail ss by (auto simp: lpc_reinterface_def)
    have src: "precise_answer_transition P ss None es"
      unfolding ss shape by (rule precise_answer_transition.unify_fail) (use unify_fail in auto)
    show ?thesis using unify_fail src tail by auto
  next
    case (meta m a gs suffix body rho)
    have shape: "e=LPCGoals (LPCMeta a#gs)" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using meta ss by (auto simp: lpc_reinterface_def)
    have fresh: "lp_cut_fresh m (map fst ss)" using meta by (simp add: ss shape suffix)
    have src: "precise_answer_transition P ss None ((LPCGoals (body@gs),eta)#(LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule precise_answer_transition.meta) (use fresh ss shape meta in auto)
    show ?thesis using meta src rho suffix by (auto simp: lpc_reinterface_def)
  next
    case (meta_unlowerable a gs rho suffix)
    have shape: "e=LPCGoals (LPCMeta a#gs)" using meta_unlowerable ss by (auto simp: lpc_reinterface_def)
    have src: "precise_answer_transition P ss None ss"
      unfolding ss shape by (rule precise_answer_transition.meta_unlowerable) (use meta_unlowerable in auto)
    show ?thesis using meta_unlowerable src by auto
  qed (use ss in \<open>auto simp: lpc_reinterface_def intro: precise_answer_transition.intros\<close>)
qed

lemma precise_reinterface_path_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and path: "(lpc_reinterface F ss,tt)\<in>(precise_answer_steps P)\<^sup>*"
  shows "\<exists>us. (ss,us)\<in>(precise_answer_steps P)\<^sup>* \<and> lpc_reinterface F us=tt"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by auto
next
  case (step tt uu)
  obtain us where reached: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and shape: "lpc_reinterface F us=tt" using step by blast
  obtain event where event: "precise_answer_transition P (lpc_reinterface F us) event uu"
    using step shape by (auto simp: precise_answer_steps_def)
  obtain ev vs where local: "precise_answer_transition P us ev vs"
    and out: "lpc_reinterface F vs=uu"
    using precise_reinterface_reflect[OF commute event] by blast
  have edge: "(us,vs)\<in>precise_answer_steps P" using local by (auto simp: precise_answer_steps_def)
  have "(ss,vs)\<in>(precise_answer_steps P)\<^sup>*" by (rule rtrancl_into_rtrancl[OF reached edge])
  then show ?case using out by blast
qed

theorem precise_return_contract_project:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "precise_return_contract P ss R t ret"
    and bridge: "\<And>eta. (ret eta,final (F eta))\<in>R\<^sup>*"
  shows "precise_return_contract P (lpc_reinterface F ss) R t final"
proof (unfold precise_return_contract_def, intro conjI allI impI)
  show "SN_on (precise_source P) {map fst (lpc_reinterface F ss)}"
    using contract by (simp add: precise_return_contract_def)
next
  fix us tail rho
  assume path: "(lpc_reinterface F ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some rho) tail"
  obtain vs where reached: "(ss,vs)\<in>(precise_answer_steps P)\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using precise_reinterface_path_reflect[OF commute path] by blast
  have actual: "precise_answer_transition P (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where local: "precise_answer_transition P vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using precise_reinterface_reflect[OF commute actual] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have output_path: "(t,ret eta)\<in>R\<^sup>*"
    using contract reached local ev unfolding precise_return_contract_def by blast
  show "(t,final rho)\<in>R\<^sup>*"
    unfolding rho by (rule rtrancl_trans[OF output_path bridge])
qed


end
end
