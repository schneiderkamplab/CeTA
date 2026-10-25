theory LP_Dependency_Triple_Success
  imports LP_Dependency_Triple_Translation
begin

lemma lp_triple_answer_machine_step:
  assumes valid: "lp_ivalid P s"
    and step: "((lp_igoals P s,\<rho>),(gs,\<eta>)) \<in> lp_seg_answer_step P"
  obtains q t \<sigma> where
    "(s,q) \<in> (lp_ilocal P)\<^sup>*"
    "(lp_iconfig_subst q \<sigma>,t) \<in> lp_ilocal P"
    "lp_ivalid P t" "lp_igoals P t = gs"
    "lp_ianswer P t = lp_iatom_subst (lp_ianswer P s) \<sigma>"
    "\<eta> = (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
proof -
  obtain a rest c \<sigma> \<nu> where sg: "lp_igoals P s = a#rest"
    and c: "c < length P"
    and match: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
    and gs: "gs = map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) rest"
    and eta: "\<eta> = (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
    using step by (cases rule: lp_seg_answer_step.cases) auto
  obtain q where sq: "(s,q) \<in> (lp_ilocal P)\<^sup>*"
    and vq: "lp_ivalid P q" and gq: "lp_igoals P q = lp_igoals P s"
    and aq: "lp_ianswer P q = lp_ianswer P s"
    and form: "lp_ifocused q \<or> (\<exists>a. q=LPIDone a)"
    by (rule lp_inormalize_returns[OF valid]) blast
  have fq: "lp_ifocused q" using form gq sg by auto
  obtain t where qt: "(lp_iconfig_subst q \<sigma>,t) \<in> lp_ilocal P"
    and vt: "lp_ivalid P t" and gt: "lp_igoals P t = gs"
    and at: "lp_ianswer P t = lp_iatom_subst (lp_ianswer P s) \<sigma>"
    by (rule lp_ifocused_resolve[OF vq fq HOL.trans[OF gq sg] c match])
      (auto simp: gs aq)
  show thesis by (rule that[OF sq qt vt gt at eta])
qed

context lp_translation
begin

lemma lp_triple_local_links:
  assumes path: "(s,t) \<in> (lp_ilocal P)\<^sup>*"
  shows "(iencode s,iencode t) \<in> (lp_pi_link (set translated))\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step y z)
  have edge: "(iencode y,iencode z) \<in> lp_pi_link (set translated)"
    using lp_iactive_irewrite[OF ilocal_simulation[OF step.hyps(2)]]
    by (simp add: lp_pi_link_def)
  show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) edge])
qed

lemma lp_triple_success_machine:
  assumes path: "((gs,\<rho>),(hs,\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
    and valid: "lp_ivalid P s" and goals: "lp_igoals P s = gs"
    and answer: "lp_ianswer P s = lp_atom_eval a \<rho>"
  obtains t where "lp_ivalid P t" "lp_igoals P t = hs"
    "lp_ianswer P t = lp_atom_eval a \<eta>"
    "(iencode s,iencode t) \<in> (lp_pi_link (set translated))\<^sup>*"
  using path valid goals answer
proof (induct arbitrary: s thesis rule: rtrancl_induct2)
  case refl
  show ?case by (rule refl.prems(1)[OF refl.prems(2,3,4)]) simp
next
  case (step hs \<eta> ks \<tau>)
  obtain t where vt: "lp_ivalid P t" and gt: "lp_igoals P t=hs"
    and at: "lp_ianswer P t=lp_atom_eval a \<eta>"
    and st: "(iencode s,iencode t) \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule step.hyps(3)[OF _ step.prems(2,3,4)]) blast
  have transition: "((lp_igoals P t,\<eta>),(ks,\<tau>)) \<in> lp_seg_answer_step P"
    using step.hyps(2) by (simp add: gt)
  obtain q u \<sigma> where tq: "(t,q) \<in> (lp_ilocal P)\<^sup>*"
    and qu: "(lp_iconfig_subst q \<sigma>,u) \<in> lp_ilocal P"
    and vu: "lp_ivalid P u" and gu: "lp_igoals P u=ks"
    and au: "lp_ianswer P u=lp_iatom_subst (lp_ianswer P t) \<sigma>"
    and tau: "\<tau>=(\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
    by (rule lp_triple_answer_machine_step[OF vt transition]) blast
  have tq': "(iencode t,iencode q) \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule lp_triple_local_links[OF tq])
  have instantiate: "(iencode q,iencode (lp_iconfig_subst q \<sigma>))
      \<in> lp_pi_link (set translated)"
    by (auto simp: iencode_subst lp_pi_link_def)
  have local: "(iencode (lp_iconfig_subst q \<sigma>),iencode u)
      \<in> lp_pi_link (set translated)"
    using lp_iactive_irewrite[OF ilocal_simulation[OF qu]]
    by (simp add: lp_pi_link_def)
  have path: "(iencode s,iencode u) \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF rtrancl_into_rtrancl[OF
      rtrancl_trans[OF st tq'] instantiate] local])
  show ?case by (rule step.prems(1)[OF vu gu _ path])
    (simp add: au at tau)
qed

theorem lp_triple_success_links:
  assumes success: "(([lp_atom_eval a \<rho>],\<rho>),([],\<eta>))
    \<in> (lp_seg_answer_step P)\<^sup>*"
  shows "(lp_itag inp (lp_atom_eval a \<rho>),lp_itag out (lp_atom_eval a \<eta>))
    \<in> (lp_pi_link (set translated))\<^sup>*"
proof -
  obtain t where vt: "lp_ivalid P t" and gt: "lp_igoals P t=[]"
    and at: "lp_ianswer P t=lp_atom_eval a \<eta>"
    and path: "(iencode (LPICall (lp_atom_eval a \<rho>)),iencode t)
      \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule lp_triple_success_machine[OF success, of "LPICall (lp_atom_eval a \<rho>)" a]) auto
  obtain q where tq: "(t,q) \<in> (lp_ilocal P)\<^sup>*"
    and gq: "lp_igoals P q=lp_igoals P t" and aq: "lp_ianswer P q=lp_ianswer P t"
    and form: "lp_ifocused q \<or> (\<exists>a. q=LPIDone a)"
    by (rule lp_inormalize_returns[OF vt]) blast
  have q: "q=LPIDone (lp_atom_eval a \<eta>)"
    using form gt gq at aq lp_ifocused_nonempty by force
  show ?thesis using rtrancl_trans[OF path lp_triple_local_links[OF tq]] by (simp add: q)
qed

lemma lp_triple_local_capture:
  assumes path: "(s,t) \<in> (lp_ilocal P)\<^sup>*"
  shows "(LPIFun f (iencode s # saved),LPIFun f (iencode t # saved))
    \<in> (lp_pi_link (set translated))\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step y z)
  have rewrite: "(iencode y,iencode z) \<in> lp_irewrite (set translated)"
    by (rule lp_iactive_irewrite[OF ilocal_simulation[OF step.hyps(2)]])
  have edge: "(LPIFun f (iencode y # saved),LPIFun f (iencode z # saved))
      \<in> lp_irewrite (set translated)"
    using lp_irewrite.arg[of 0 "iencode y # saved" "iencode z" "set translated" f]
      rewrite by simp
  show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3)])
    (use edge in \<open>simp add: lp_pi_link_def\<close>)
qed

lemma lp_triple_success_captured_machine:
  assumes path: "((gs,\<rho>),(hs,\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
    and valid: "lp_ivalid P s" and goals: "lp_igoals P s = gs"
    and answer: "lp_ianswer P s = lp_atom_eval a \<rho>"
  obtains t where "lp_ivalid P t" "lp_igoals P t = hs"
    "lp_ianswer P t = lp_atom_eval a \<eta>"
    "(LPIFun f (iencode s # map \<rho> saved),LPIFun f (iencode t # map \<eta> saved))
      \<in> (lp_pi_link (set translated))\<^sup>*"
  using path valid goals answer
proof (induct arbitrary: s thesis rule: rtrancl_induct2)
  case refl
  show ?case by (rule refl.prems(1)[OF refl.prems(2,3,4)]) simp
next
  case (step hs \<eta> ks \<tau>)
  obtain t where vt: "lp_ivalid P t" and gt: "lp_igoals P t=hs"
    and at: "lp_ianswer P t=lp_atom_eval a \<eta>"
    and st: "(LPIFun f (iencode s # map \<rho> saved),LPIFun f (iencode t # map \<eta> saved))
      \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule step.hyps(3)[OF _ step.prems(2,3,4)]) blast
  have transition: "((lp_igoals P t,\<eta>),(ks,\<tau>)) \<in> lp_seg_answer_step P"
    using step.hyps(2) by (simp add: gt)
  obtain q u \<sigma> where tq: "(t,q) \<in> (lp_ilocal P)\<^sup>*"
    and qu: "(lp_iconfig_subst q \<sigma>,u) \<in> lp_ilocal P"
    and vu: "lp_ivalid P u" and gu: "lp_igoals P u=ks"
    and au: "lp_ianswer P u=lp_iatom_subst (lp_ianswer P t) \<sigma>"
    and tau: "\<tau>=(\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
    by (rule lp_triple_answer_machine_step[OF vt transition]) blast
  have tq': "(LPIFun f (iencode t # map \<eta> saved),LPIFun f (iencode q # map \<eta> saved))
      \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule lp_triple_local_capture[OF tq])
  have instantiate: "(LPIFun f (iencode q # map \<eta> saved),
      LPIFun f (iencode (lp_iconfig_subst q \<sigma>) # map \<tau> saved))
      \<in> lp_pi_link (set translated)"
  proof -
    have eq: "LPIFun f (iencode (lp_iconfig_subst q \<sigma>) # map \<tau> saved) =
      lp_isubst (LPIFun f (iencode q # map \<eta> saved)) \<sigma>"
      by (simp add: tau iencode_subst o_def)
    show ?thesis unfolding lp_pi_link_def using eq by blast
  qed
  have local: "(LPIFun f (iencode (lp_iconfig_subst q \<sigma>) # map \<tau> saved),
      LPIFun f (iencode u # map \<tau> saved))
      \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule lp_triple_local_capture[OF r_into_rtrancl[OF qu]])
  have path: "(LPIFun f (iencode s # map \<rho> saved),LPIFun f (iencode u # map \<tau> saved))
      \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule rtrancl_trans[OF rtrancl_into_rtrancl[OF rtrancl_trans[OF st tq'] instantiate] local])
  show ?case by (rule step.prems(1)[OF vu gu _ path]) (simp add: au at tau)
qed

theorem lp_triple_success_capture:
  assumes success: "(([lp_atom_eval a \<rho>],\<rho>),([],\<eta>))
    \<in> (lp_seg_answer_step P)\<^sup>*"
  shows "(LPIFun f (lp_itag inp (lp_atom_eval a \<rho>) # map \<rho> saved),
    LPIFun f (lp_itag out (lp_atom_eval a \<eta>) # map \<eta> saved))
    \<in> (lp_pi_link (set translated))\<^sup>*"
proof -
  obtain t where vt: "lp_ivalid P t" and gt: "lp_igoals P t=[]"
    and at: "lp_ianswer P t=lp_atom_eval a \<eta>"
    and path: "(LPIFun f (iencode (LPICall (lp_atom_eval a \<rho>)) # map \<rho> saved),
      LPIFun f (iencode t # map \<eta> saved)) \<in> (lp_pi_link (set translated))\<^sup>*"
    by (rule lp_triple_success_captured_machine[OF success, of "LPICall (lp_atom_eval a \<rho>)" a f saved]) auto
  obtain q where tq: "(t,q) \<in> (lp_ilocal P)\<^sup>*"
    and gq: "lp_igoals P q=lp_igoals P t" and aq: "lp_ianswer P q=lp_ianswer P t"
    and form: "lp_ifocused q \<or> (\<exists>a. q=LPIDone a)"
    by (rule lp_inormalize_returns[OF vt]) blast
  have q: "q=LPIDone (lp_atom_eval a \<eta>)"
    using form gt gq at aq lp_ifocused_nonempty by force
  show ?thesis using rtrancl_trans[OF path lp_triple_local_capture[OF tq]] by (simp add: q)
qed

end
end
