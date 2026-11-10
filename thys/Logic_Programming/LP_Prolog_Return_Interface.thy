theory LP_Prolog_Return_Interface
 imports LP_Prolog_Domain_Composition LP_Cut_Return_Interface_Lift
begin

lemma lpp_reinterface_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "lpp_answer_transition P B U ss event tt"
  shows "lpp_answer_transition P B U (lpc_reinterface F ss) (map_option F event) (lpc_reinterface F tt)"
  using step
proof (cases rule: lpp_answer_transition.cases)
  case base
  show ?thesis by (rule lpp_answer_transition.base)
    (use base lpc_reinterface_forward[where F=F, OF commute base(2)] in auto)
qed (auto simp: lpc_reinterface_def commute map_map o_def case_prod_unfold intro: lpp_answer_transition.intros)

lemma lpp_reinterface_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "lpp_answer_transition P B U (lpc_reinterface F ss) event tt"
  shows "\<exists>ev us. lpp_answer_transition P B U ss ev us \<and>
    map_option F ev = event \<and> lpc_reinterface F us = tt"
proof -
  have nonempty: "ss\<noteq>[]" using step
    by (auto simp: lpc_reinterface_def elim: lpp_answer_transition.cases lpc_answer_transition.cases)
  obtain e eta es where ss: "ss = (e,eta)#es" using nonempty by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof (cases rule: lpp_answer_transition.cases)
    case base
    obtain ev us where local: "lpc_answer_transition P ss ev us"
      and event: "map_option F ev = event" and shape: "lpc_reinterface F us = tt"
      using lpc_reinterface_reflect[where F=F, OF commute base(2)] by blast
    have clear: "\<not>lpp_builtin_active B (map fst ss)" using base(1) by simp
    show ?thesis using lpp_answer_transition.base[OF clear local] event shape by blast
  next
    case (success f ts sigma gs rho tail)
    have shape: "e = LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)"
      and rho: "rho = F eta" and tail: "tail = lpc_reinterface F es"
      using success ss by (auto simp: lpc_reinterface_def)
    have local: "lpp_answer_transition P B U ss None
      ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
        \<lambda>x. lp_isubst (eta x) sigma)#es)"
      unfolding ss shape by (rule lpp_answer_transition.success) (use success in auto)
    show ?thesis using success local rho tail by (auto simp: lpc_reinterface_def commute)
  next
    case failure
    then show ?thesis using ss
      by (auto simp: lpc_reinterface_def intro: lpp_answer_transition.failure)
  next
    case error
    then show ?thesis using ss
      by (auto simp: lpc_reinterface_def intro: lpp_answer_transition.error)
  next
    case (probe f ts a keep m gs tail n rho)
    have shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)"
      and rho: "rho=F eta" and tail: "tail=lpc_reinterface F es"
      using probe ss by (auto simp: lpc_reinterface_def)
    have fm: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es)"
      using probe(5) tail by simp
    have fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es)"
      using probe(6) tail by simp
    have local: "lpp_answer_transition P B U ss None
      ((LPCGoals (lpp_probe_goals a keep m gs),eta)#(LPCBarrier n,eta)#
        (LPCGoals (lpp_probe_else keep gs),eta)#(LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule lpp_answer_transition.probe) (rule probe(4), rule fm, rule fn)
    show ?thesis using probe local rho tail by (auto simp: lpc_reinterface_def)
  next
    case (branch f ts cs ys ns m gs tail n rho)
    have shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)"
      and rho: "rho=F eta" and tail: "tail=lpc_reinterface F es"
      using branch ss by (auto simp: lpc_reinterface_def)
    have fm: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es)"
      using branch(6) tail by simp
    have fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es)"
      using branch(7) tail by simp
    have local: "lpp_answer_transition P B U ss None
      ((LPCGoals (cs@(LPCCut m#(ys@gs))),eta)#(LPCBarrier n,eta)#
        (LPCGoals (ns@gs),eta)#(LPCBarrier m,eta)#es)"
      unfolding ss shape by (rule lpp_answer_transition.branch) (rule branch(4), rule branch(5), rule fm, rule fn)
    show ?thesis using branch local rho tail by (auto simp: lpc_reinterface_def)
  next
    case call
    then show ?thesis using ss by (auto simp: lpc_reinterface_def lpc_attach_answers_def intro: lpp_answer_transition.call)
  qed
qed

lemma lpp_domain_reinterface_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "lpp_domain_answers P B U D ss event tt"
  shows "lpp_domain_answers P B U D (lpc_reinterface F ss) (map_option F event) (lpc_reinterface F tt)"
  using step lpp_reinterface_forward[where F=F, OF commute]
  by (auto simp: lpp_domain_answers_def)

lemma lpp_domain_reinterface_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "lpp_domain_answers P B U D (lpc_reinterface F ss) event tt"
  shows "\<exists>ev us. lpp_domain_answers P B U D ss ev us \<and>
    map_option F ev = event \<and> lpc_reinterface F us = tt"
proof (cases "lpp_answer_transition P B U (lpc_reinterface F ss) event tt")
  case True
  show ?thesis using lpp_reinterface_reflect[where F=F, OF commute True] by (auto simp: lpp_domain_answers_def)
next
  case False
  have "lpp_builtin_domain_bad B D (map fst ss)" "event = None" "tt = lpc_reinterface F ss"
    using step False by (auto simp: lpp_domain_answers_def)
  then show ?thesis by (intro exI[of _ None] exI[of _ ss]) (simp add: lpp_domain_answers_def)
qed

lemma lpp_domain_contract_project:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
    and bridge: "\<And>eta. (ret eta,final (F eta))\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_reinterface F ss) R t final"
proof (rule lp_answer_contract_simulation[where rep="\<lambda>us vs. lpc_reinterface F us = vs"
    and outputs="\<lambda>a b. b = F a", OF contract refl])
  fix us vs event ws
  assume shape: "lpc_reinterface F us = vs" and step: "lpp_domain_answers P B U D vs event ws"
  obtain ev zs where local: "lpp_domain_answers P B U D us ev zs"
    and out: "map_option F ev = event" and target: "lpc_reinterface F zs = ws"
    using lpp_domain_reinterface_reflect[where F=F, OF commute, of P B U D us event ws] step shape by blast
  show "\<exists>ev zs. lpp_domain_answers P B U D us ev zs \<and> lpc_reinterface F zs = ws \<and>
    (\<forall>beta. event = Some beta \<longrightarrow> (\<exists>alpha. ev = Some alpha \<and> beta = F alpha))"
    using local out target by (cases ev) auto
qed (use bridge in auto)

lemma lpp_domain_contract_lift_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lp_answer_contract (lpp_domain_answers P B U D) (lpc_reinterface F ss) R t ret"
    and bridge: "\<And>eta. (ret (F eta),final eta)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P B U D) ss R t final"
proof (rule lp_answer_contract_simulation[where rep="\<lambda>us vs. us = lpc_reinterface F vs"
    and outputs="\<lambda>a b. a = F b", OF contract refl])
  fix us vs event ws
  assume shape: "us = lpc_reinterface F vs" and step: "lpp_domain_answers P B U D vs event ws"
  have local: "lpp_domain_answers P B U D us (map_option F event) (lpc_reinterface F ws)"
    using lpp_domain_reinterface_forward[where F=F, OF commute step] shape by simp
  show "\<exists>ev zs. lpp_domain_answers P B U D us ev zs \<and> zs = lpc_reinterface F ws \<and>
    (\<forall>beta. event = Some beta \<longrightarrow> (\<exists>alpha. ev = Some alpha \<and> alpha = F beta))"
    by (intro exI[of _ "map_option F event"] exI[of _ "lpc_reinterface F ws"])
      (use local in auto)
qed (use bridge in auto)

end
