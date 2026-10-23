theory LP_Cut_Return_Interface
  imports LP_Cut_Return_Modular LP_Cut_Return_State
begin

definition lpc_reinterface where
  "lpc_reinterface F ss = map (\<lambda>(e,eta). (e,F eta)) ss"

lemma lpc_reinterface_erases[simp]:
  "map fst (lpc_reinterface F ss) = map fst ss"
  by (simp add: lpc_reinterface_def map_map o_def split_def)

lemma lpc_reinterface_prune:
  "lpc_reinterface F (lpc_answer_prune m ss) = lpc_answer_prune m (lpc_reinterface F ss)"
  by (induct ss) (auto simp: lpc_reinterface_def split: prod.splits lp_cut_entry.splits)

text \<open>Interface projection changes observations, never source execution.
Its substitution law is explicit, including the values outside a finite tuple.
Every observed transition lifts to the unprojected execution with the same
source unifier, even when multiple environments have the same projection.\<close>

lemma lpc_reinterface_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "lpc_answer_transition P (lpc_reinterface F ss) event tt"
  shows "\<exists>ev us. lpc_answer_transition P ss ev us \<and>
    map_option F ev=event \<and> lpc_reinterface F us=tt"
proof -
  have nonempty: "ss\<noteq>[]" using step
    by (auto simp: lpc_reinterface_def elim: lpc_answer_transition.cases)
  obtain e eta es where ss: "ss=(e,eta)#es" using nonempty by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof (cases rule: lpc_answer_transition.cases)
    case (cut m gs rho suffix)
    have shape: "e=LPCGoals (LPCCut m#gs)" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using cut ss by (auto simp: lpc_reinterface_def)
    have src: "lpc_answer_transition P ss None ((LPCGoals gs,eta)#lpc_answer_prune m es)"
      unfolding ss shape by (rule lpc_answer_transition.cut)
    show ?thesis using cut src rho suffix lpc_reinterface_prune[of F m es]
      by (auto simp: lpc_reinterface_def)
  next
    case (case_call m f ts gs suffix rho)
    have shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using case_call ss by (auto simp: lpc_reinterface_def)
    have fresh: "lp_cut_fresh m (map fst ss)"
      using case_call by (simp add: ss shape suffix)
    have src: "lpc_answer_transition P ss None
      (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m,eta))
        (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule lpc_answer_transition.case_call) (use fresh ss shape in simp)
    show ?thesis using case_call src rho suffix
      by (auto simp: lpc_reinterface_def map_map o_def)
  next
    case (resolve c a gs sigma nu m rho suffix)
    have shape: "e=LPCClause (LPCAtom a#gs) c m" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using resolve ss by (auto simp: lpc_reinterface_def)
    have src: "lpc_answer_transition P ss None
      ((LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t nu)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),\<lambda>x. lp_isubst (eta x) sigma)#es)"
      unfolding ss shape by (rule lpc_answer_transition.resolve) (use resolve in auto)
    show ?thesis using resolve src rho suffix
      by (auto simp: lpc_reinterface_def commute)
  next
    case (backtrack c a gs m rho)
    have shape: "e=LPCClause (LPCAtom a#gs) c m" and tail: "tt=lpc_reinterface F es"
      using backtrack ss by (auto simp: lpc_reinterface_def)
    have src: "lpc_answer_transition P ss None es"
      unfolding ss shape by (rule lpc_answer_transition.backtrack) (use backtrack in auto)
    show ?thesis using backtrack src tail by auto
  next
    case (unify a b gs sigma rho suffix)
    have shape: "e=LPCGoals (LPCUnify a b#gs)" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using unify ss by (auto simp: lpc_reinterface_def)
    have src: "lpc_answer_transition P ss None
      ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),\<lambda>x. lp_isubst (eta x) sigma)#es)"
      unfolding ss shape by (rule lpc_answer_transition.unify) (use unify in auto)
    show ?thesis using unify src rho suffix by (auto simp: lpc_reinterface_def commute)
  next
    case (unify_fail a b gs rho)
    have shape: "e=LPCGoals (LPCUnify a b#gs)" and tail: "tt=lpc_reinterface F es"
      using unify_fail ss by (auto simp: lpc_reinterface_def)
    have src: "lpc_answer_transition P ss None es"
      unfolding ss shape by (rule lpc_answer_transition.unify_fail) (use unify_fail in auto)
    show ?thesis using unify_fail src tail by auto
  next
    case (meta m a gs suffix body rho)
    have shape: "e=LPCGoals (LPCMeta a#gs)" and rho: "rho=F eta"
      and suffix: "suffix=lpc_reinterface F es"
      using meta ss by (auto simp: lpc_reinterface_def)
    have fresh: "lp_cut_fresh m (map fst ss)" using meta by (simp add: ss shape suffix)
    have src: "lpc_answer_transition P ss None ((LPCGoals (body@gs),eta)#(LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule lpc_answer_transition.meta) (use fresh ss shape meta in auto)
    show ?thesis using meta src rho suffix by (auto simp: lpc_reinterface_def)
  next
    case (meta_unlowerable a gs rho suffix)
    have shape: "e=LPCGoals (LPCMeta a#gs)" using meta_unlowerable ss by (auto simp: lpc_reinterface_def)
    have src: "lpc_answer_transition P ss None ss"
      unfolding ss shape by (rule lpc_answer_transition.meta_unlowerable) (use meta_unlowerable in auto)
    show ?thesis using meta_unlowerable src by auto
  qed (use ss in \<open>auto simp: lpc_reinterface_def intro: lpc_answer_transition.intros\<close>)
qed

lemma lpc_reinterface_path_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and path: "(lpc_reinterface F ss,tt)\<in>(lpc_answer_steps P)\<^sup>*"
  shows "\<exists>us. (ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<and> lpc_reinterface F us=tt"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by auto
next
  case (step tt uu)
  obtain us where reached: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and shape: "lpc_reinterface F us=tt" using step by blast
  obtain event where event: "lpc_answer_transition P (lpc_reinterface F us) event uu"
    using step shape by (auto simp: lpc_answer_steps_def)
  obtain ev vs where local: "lpc_answer_transition P us ev vs"
    and out: "lpc_reinterface F vs=uu"
    using lpc_reinterface_reflect[OF commute event] by blast
  have edge: "(us,vs)\<in>lpc_answer_steps P" using local by (auto simp: lpc_answer_steps_def)
  have "(ss,vs)\<in>(lpc_answer_steps P)\<^sup>*" by (rule rtrancl_into_rtrancl[OF reached edge])
  then show ?case using out by blast
qed

theorem lpc_return_contract_project:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpc_return_contract P ss R t ret"
    and bridge: "\<And>eta. (ret eta,final (F eta))\<in>R\<^sup>*"
  shows "lpc_return_contract P (lpc_reinterface F ss) R t final"
proof (unfold lpc_return_contract_def, intro conjI allI impI)
  show "SN_on (lp_cut_mgu_source P) {map fst (lpc_reinterface F ss)}"
    using contract by (simp add: lpc_return_contract_def)
next
  fix us tail rho
  assume path: "(lpc_reinterface F ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some rho) tail"
  obtain vs where reached: "(ss,vs)\<in>(lpc_answer_steps P)\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpc_reinterface_path_reflect[OF commute path] by blast
  have actual: "lpc_answer_transition P (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where local: "lpc_answer_transition P vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using lpc_reinterface_reflect[OF commute actual] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have output_path: "(t,ret eta)\<in>R\<^sup>*"
    using contract reached local ev unfolding lpc_return_contract_def by blast
  show "(t,final rho)\<in>R\<^sup>*"
    unfolding rho by (rule rtrancl_trans[OF output_path bridge])
qed

definition lpc_project_interface where
  "lpc_project_interface indices eta n =
    (if n<length indices then eta (indices!n) else LPIFun LPCTruth [])"

lemma lpc_project_interface_commutes:
  "lpc_project_interface indices (\<lambda>x. lp_isubst (eta x) sigma) =
    (\<lambda>n. lp_isubst (lpc_project_interface indices eta n) sigma)"
  by (rule ext) (simp add: lpc_project_interface_def)

lemma lpc_project_finite_interface:
  assumes bounds: "list_all (\<lambda>i. i<length ts) indices"
  shows "lpc_project_interface indices (lpc_return_env ts eta) =
    lpc_return_env (map ((!) ts) indices) eta"
proof (rule ext)
  fix n
  have "n<length indices \<Longrightarrow> indices!n<length ts"
    using bounds by (auto simp: list_all_iff)
  then show "lpc_project_interface indices (lpc_return_env ts eta) n =
    lpc_return_env (map ((!) ts) indices) eta n"
    by (simp add: lpc_project_interface_def lpc_return_env_def)
qed

definition lpc_check_return_projection where
  "lpc_check_return_projection indices ss tt =
    (list_all (\<lambda>frame. list_all (\<lambda>i. i<length (snd frame)) indices) ss \<and>
     tt=map (\<lambda>(e,ts). (e,map ((!) ts) indices)) ss)"

lemma lpc_check_return_projection_sound:
  assumes "lpc_check_return_projection indices ss tt"
  shows "lpc_return_eval eta tt =
    lpc_reinterface (lpc_project_interface indices) (lpc_return_eval eta ss)"
  using assms
  unfolding lpc_check_return_projection_def lpc_return_eval_def lpc_reinterface_def
  by (auto simp: map_map o_def split_def list_all_iff
    intro!: map_cong lpc_project_finite_interface[symmetric])

end
