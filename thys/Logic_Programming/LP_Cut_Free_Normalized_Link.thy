theory LP_Cut_Free_Normalized_Link
  imports LP_Cut_MGU_Link
begin

lemma lpc_free_normalized_source:
  assumes normalized: "lp_cut_normalize fuel equations (map (\<lambda>x. LPCAtom (Var x)) (remdups F)) = Some (Some gs)"
    and extracted: "lpc_free_goal_vars gs=Some xs"
    and equations: "lp_equations equations eta"
    and known: "lpc_free_knowledge (set F) eta"
  shows "lpc_free_knowledge (set xs) eta"
proof -
  have shape: "gs=map (\<lambda>x. LPCAtom (Var x)) xs"
    by (rule lpc_free_goal_vars_sound[OF extracted])
  have same: "map eta (remdups F)=map eta xs"
    using lp_cut_normalized_terms[OF equations, of fuel "map Var (remdups F)" "map Var xs"] normalized shape
    by (simp add: map_map o_def)
  have variables: "list_all (\<lambda>t. \<exists>v. t=LPIVar v) (map eta (remdups F))"
    using known by (simp add: lpc_free_knowledge_def list_all_iff)
  have distinct: "distinct (map eta (remdups F))"
    using known by (simp add: lpc_free_knowledge_def distinct_map)
  have target_vars: "\<forall>x\<in>set xs. \<exists>v. eta x=LPIVar v"
    using variables by (simp add: same list_all_iff)
  have target_inj: "inj_on eta (set xs)" using distinct by (simp add: same distinct_map)
  show ?thesis using target_vars target_inj by (simp add: lpc_free_knowledge_def)
qed

definition lpc_check_link_free_normalized where
  "lpc_check_link_free_normalized fuel equations F H bindings =
    (case lp_cut_normalize fuel equations (map (\<lambda>x. LPCAtom (Var x)) (remdups F)) of
      Some (Some gs) \<Rightarrow> (case lpc_free_goal_vars gs of
        Some xs \<Rightarrow> lpc_check_link_free fuel equations xs H bindings | _ \<Rightarrow> False)
      | _ \<Rightarrow> False)"

lemma lpc_checked_link_free_normalized_sound:
  assumes checked: "lpc_check_link_free_normalized fuel equations F H bindings"
    and equations: "lp_equations equations eta"
    and known: "lpc_free_knowledge (set F) eta"
  shows "lpc_free_knowledge (set H) (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
proof -
  obtain gs xs where normalized:
    "lp_cut_normalize fuel equations (map (\<lambda>x. LPCAtom (Var x)) (remdups F))=Some (Some gs)"
    and extracted: "lpc_free_goal_vars gs=Some xs"
    and target: "lpc_check_link_free fuel equations xs H bindings"
    using checked by (auto simp: lpc_check_link_free_normalized_def split: option.splits)
  have source: "lpc_free_knowledge (set xs) eta"
    by (rule lpc_free_normalized_source[OF normalized extracted equations known])
  show ?thesis by (rule lpc_checked_link_free_sound[OF target equations source])
qed

end
