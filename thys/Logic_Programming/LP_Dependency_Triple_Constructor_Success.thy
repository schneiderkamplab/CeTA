theory LP_Dependency_Triple_Constructor_Success
  imports LP_Dependency_Triple_Data LP_Dependency_Triple_Success
begin

context lp_translation
begin

lemma lp_triple_data_local_links:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U"
    and path: "(s,t)\<in>(lp_ilocal P)\<^sup>*"
  shows "(iencode (lp_data_config data s),iencode (lp_data_config data t))
    \<in>(lp_clink C (set translated) U)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step y z)
  have edge: "(iencode (lp_data_config data y),iencode (lp_data_config data z))
    \<in>lp_clink C (set translated) U"
    using data_ilocal_constructor[OF fixed range shapes frames step.hyps(2)]
    by (simp add: lp_clink_def)
  show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) edge])
qed

lemma lp_triple_data_success_machine:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U"
    and path: "((gs,\<rho>),(hs,\<eta>))\<in>(lp_seg_answer_step P)\<^sup>*"
    and valid: "lp_ivalid P s" and goals: "lp_igoals P s=gs"
    and answer: "lp_ianswer P s=lp_atom_eval a \<rho>"
  obtains t where "lp_ivalid P t" "lp_igoals P t=hs"
    "lp_ianswer P t=lp_atom_eval a \<eta>"
    "(iencode (lp_data_config data s),iencode (lp_data_config data t))
      \<in>(lp_clink C (set translated) U)\<^sup>*"
  using path valid goals answer
proof (induct arbitrary: s thesis rule: rtrancl_induct2)
  case refl
  show ?case by (rule refl.prems(1)[OF refl.prems(2,3,4)]) simp
next
  case (step hs \<eta> ks \<tau>)
  obtain t where vt: "lp_ivalid P t" and gt: "lp_igoals P t=hs"
    and at: "lp_ianswer P t=lp_atom_eval a \<eta>"
    and st: "(iencode (lp_data_config data s),iencode (lp_data_config data t))
      \<in>(lp_clink C (set translated) U)\<^sup>*"
    by (rule step.hyps(3)[OF _ step.prems(2,3,4)]) blast
  have transition: "((lp_igoals P t,\<eta>),(ks,\<tau>))\<in>lp_seg_answer_step P"
    using step.hyps(2) by (simp add: gt)
  obtain q u' \<sigma> where tq: "(t,q)\<in>(lp_ilocal P)\<^sup>*"
    and qu: "(lp_iconfig_subst q \<sigma>,u')\<in>lp_ilocal P"
    and vu: "lp_ivalid P u'" and gu: "lp_igoals P u'=ks"
    and au: "lp_ianswer P u'=lp_iatom_subst (lp_ianswer P t) \<sigma>"
    and tau: "\<tau>=(\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
    by (rule lp_triple_answer_machine_step[OF vt transition]) blast
  have tq': "(iencode (lp_data_config data t),iencode (lp_data_config data q))
    \<in>(lp_clink C (set translated) U)\<^sup>*"
    by (rule lp_triple_data_local_links[OF fixed range shapes frames tq])
  have instantiate: "(iencode (lp_data_config data q),
      iencode (lp_data_config data (lp_iconfig_subst q \<sigma>)))
      \<in>lp_clink C (set translated) U"
    by (auto simp: lp_data_config_subst iencode_subst lp_clink_def)
  have local: "(iencode (lp_data_config data (lp_iconfig_subst q \<sigma>)),
      iencode (lp_data_config data u'))\<in>lp_clink C (set translated) U"
    using data_ilocal_constructor[OF fixed range shapes frames qu]
    by (simp add: lp_clink_def)
  have path: "(iencode (lp_data_config data s),iencode (lp_data_config data u'))
    \<in>(lp_clink C (set translated) U)\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF rtrancl_into_rtrancl[OF
      rtrancl_trans[OF st tq'] instantiate] local])
  show ?case by (rule step.prems(1)[OF vu gu _ path])
    (simp add: au at tau lp_atom_eval_subst)
qed


lemma lp_triple_data_local_capture:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U" and capture: "f\<in>U"
    and path: "(s,t)\<in>(lp_ilocal P)\<^sup>*"
  shows "(LPIFun f (iencode (lp_data_config data s)#saved),
    LPIFun f (iencode (lp_data_config data t)#saved))
    \<in>(lp_clink C (set translated) U)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step y z)
  have local: "(iencode (lp_data_config data y),iencode (lp_data_config data z))
    \<in>lp_cactive C (set translated) U"
    by (rule data_ilocal_constructor[OF fixed range shapes frames step.hyps(2)])
  have edge: "(LPIFun f (iencode (lp_data_config data y)#saved),
      LPIFun f (iencode (lp_data_config data z)#saved))\<in>lp_clink C (set translated) U"
    using lp_cactive.frame[OF capture local] by (simp add: lp_clink_def)
  show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) edge])
qed

lemma lp_triple_data_success_captured_machine:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U" and capture: "f\<in>U"
    and path: "((gs,\<rho>),(hs,\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
    and valid: "lp_ivalid P s" and goals: "lp_igoals P s = gs"
    and answer: "lp_ianswer P s = lp_atom_eval a \<rho>"
  obtains t where "lp_ivalid P t" "lp_igoals P t = hs"
    "lp_ianswer P t = lp_atom_eval a \<eta>"
    "(LPIFun f (iencode (lp_data_config data s) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) saved),LPIFun f (iencode (lp_data_config data t) # map (\<lambda>x. map_lp_iterm data id (\<eta> x)) saved))
      \<in> (lp_clink C (set translated) U)\<^sup>*"
  using path valid goals answer
proof (induct arbitrary: s thesis rule: rtrancl_induct2)
  case refl
  show ?case by (rule refl.prems(1)[OF refl.prems(2,3,4)]) simp
next
  case (step hs \<eta> ks \<tau>)
  obtain t where vt: "lp_ivalid P t" and gt: "lp_igoals P t=hs"
    and at: "lp_ianswer P t=lp_atom_eval a \<eta>"
    and st: "(LPIFun f (iencode (lp_data_config data s) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) saved),LPIFun f (iencode (lp_data_config data t) # map (\<lambda>x. map_lp_iterm data id (\<eta> x)) saved))
      \<in> (lp_clink C (set translated) U)\<^sup>*"
    by (rule step.hyps(3)[OF _ step.prems(2,3,4)]) blast
  have transition: "((lp_igoals P t,\<eta>),(ks,\<tau>)) \<in> lp_seg_answer_step P"
    using step.hyps(2) by (simp add: gt)
  obtain q u \<sigma> where tq: "(t,q) \<in> (lp_ilocal P)\<^sup>*"
    and qu: "(lp_iconfig_subst q \<sigma>,u) \<in> lp_ilocal P"
    and vu: "lp_ivalid P u" and gu: "lp_igoals P u=ks"
    and au: "lp_ianswer P u=lp_iatom_subst (lp_ianswer P t) \<sigma>"
    and tau: "\<tau>=(\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
    by (rule lp_triple_answer_machine_step[OF vt transition]) blast
  have tq': "(LPIFun f (iencode (lp_data_config data t) # map (\<lambda>x. map_lp_iterm data id (\<eta> x)) saved),LPIFun f (iencode (lp_data_config data q) # map (\<lambda>x. map_lp_iterm data id (\<eta> x)) saved))
      \<in> (lp_clink C (set translated) U)\<^sup>*"
    by (rule lp_triple_data_local_capture[OF fixed range shapes frames capture tq])
  have instantiate: "(LPIFun f (iencode (lp_data_config data q) # map (\<lambda>x. map_lp_iterm data id (\<eta> x)) saved),
      LPIFun f (iencode (lp_data_config data (lp_iconfig_subst q \<sigma>)) # map (\<lambda>x. map_lp_iterm data id (\<tau> x)) saved))
      \<in> lp_clink C (set translated) U"
  proof -
    have eq: "LPIFun f (iencode (lp_data_config data (lp_iconfig_subst q \<sigma>)) # map (\<lambda>x. map_lp_iterm data id (\<tau> x)) saved) =
      lp_isubst (LPIFun f (iencode (lp_data_config data q) # map (\<lambda>x. map_lp_iterm data id (\<eta> x)) saved)) (\<lambda>x. map_lp_iterm data id (\<sigma> x))"
      by (simp add: tau lp_data_config_subst iencode_subst lp_data_map_subst map_map o_def)
    show ?thesis unfolding lp_clink_def using eq by blast
  qed
  have local: "(LPIFun f (iencode (lp_data_config data (lp_iconfig_subst q \<sigma>)) # map (\<lambda>x. map_lp_iterm data id (\<tau> x)) saved),
      LPIFun f (iencode (lp_data_config data u) # map (\<lambda>x. map_lp_iterm data id (\<tau> x)) saved))
      \<in> (lp_clink C (set translated) U)\<^sup>*"
    by (rule lp_triple_data_local_capture[OF fixed range shapes frames capture r_into_rtrancl[OF qu]])
  have path: "(LPIFun f (iencode (lp_data_config data s) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) saved),LPIFun f (iencode (lp_data_config data u) # map (\<lambda>x. map_lp_iterm data id (\<tau> x)) saved))
      \<in> (lp_clink C (set translated) U)\<^sup>*"
    by (rule rtrancl_trans[OF rtrancl_into_rtrancl[OF rtrancl_trans[OF st tq'] instantiate] local])
  show ?case by (rule step.prems(1)[OF vu gu _ path]) (simp add: au at tau)
qed


theorem lp_triple_data_success_capture:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U" and capture: "f\<in>U"
    and success: "(([lp_atom_eval a \<rho>],\<rho>),([],\<eta>))\<in>(lp_seg_answer_step P)\<^sup>*"
  shows "(LPIFun f (lp_itag inp (lp_data_atom data (lp_atom_eval a \<rho>)) #
      map (\<lambda>x. map_lp_iterm data id (\<rho> x)) saved),
    LPIFun f (lp_itag out (lp_data_atom data (lp_atom_eval a \<eta>)) #
      map (\<lambda>x. map_lp_iterm data id (\<eta> x)) saved))
    \<in>(lp_clink C (set translated) U)\<^sup>*"
proof -
  obtain t where vt: "lp_ivalid P t" and gt: "lp_igoals P t=[]"
    and at: "lp_ianswer P t=lp_atom_eval a \<eta>"
    and path: "(LPIFun f (iencode (lp_data_config data (LPICall (lp_atom_eval a \<rho>))) #
        map (\<lambda>x. map_lp_iterm data id (\<rho> x)) saved),
      LPIFun f (iencode (lp_data_config data t) # map (\<lambda>x. map_lp_iterm data id (\<eta> x)) saved))
      \<in>(lp_clink C (set translated) U)\<^sup>*"
    by (rule lp_triple_data_success_captured_machine[where s="LPICall (lp_atom_eval a \<rho>)"
      and a=a and saved=saved, OF fixed range shapes frames capture success]) auto
  obtain q where tq: "(t,q)\<in>(lp_ilocal P)\<^sup>*"
    and gq: "lp_igoals P q=lp_igoals P t" and aq: "lp_ianswer P q=lp_ianswer P t"
    and form: "lp_ifocused q \<or> (\<exists>a. q=LPIDone a)"
    by (rule lp_inormalize_returns[OF vt]) blast
  have q: "q=LPIDone (lp_atom_eval a \<eta>)"
    using form gt gq at aq lp_ifocused_nonempty by force
  show ?thesis using rtrancl_trans[OF path
    lp_triple_data_local_capture[OF fixed range shapes frames capture tq]]
    by (simp add: q)
qed

end
end
