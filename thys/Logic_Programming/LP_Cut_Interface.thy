theory LP_Cut_Interface
  imports LP_Cut_Instance
begin

lemma lp_cut_zip_valuation:
  "map (\<lambda>t. lp_ieval t \<eta>) ts=map \<eta> vs \<Longrightarrow>
    list_all (\<lambda>(x,t). lp_ieval t \<eta>=\<eta> x) (zip vs ts)"
  by (induct vs arbitrary: ts) (auto split: list.splits)

lemma lp_cut_binding_valuation:
  assumes "list_all (\<lambda>(x,t). lp_ieval t \<eta>=\<eta> x) bindings"
  shows "lp_ieval (lp_cut_instance_subst bindings x) \<eta>=\<eta> x"
  using assms
  by (induct bindings) (auto simp: lp_cut_instance_subst_def split: prod.splits if_splits)

theorem lp_cut_normalized_interface_valuation:
  assumes equations: "lp_equations eqs \<eta>"
    and checked: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) vs) =
      Some (Some (map LPCAtom ts))"
  shows "lp_ieval (lp_cut_instance_subst (zip vs ts) x) \<eta>=\<eta> x"
proof -
  have eq: "map (\<lambda>t. lp_ieval t \<eta>) ts=map \<eta> vs"
    using lp_cut_normalized_terms[OF equations, of fuel "map Var vs" ts] checked
    by (simp add: map_map o_def)
  show ?thesis by (rule lp_cut_binding_valuation[OF lp_cut_zip_valuation[OF eq]])
qed

theorem lp_cut_normalized_interface_state:
  assumes equations: "lp_equations eqs \<eta>"
    and checked: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) vs) =
      Some (Some (map LPCAtom ts))"
  shows "lp_cut_state_eval
    (lp_cut_state_map (\<lambda>t. t\<cdot>lp_cut_instance_subst (zip vs ts)) s) \<eta> = lp_cut_state_eval s \<eta>"
  by (simp add: lp_cut_state_eval_subst lp_cut_normalized_interface_valuation[OF equations checked])

theorem lp_cut_normalized_interface_guard:
  assumes equations: "lp_equations eqs \<eta>"
    and checked: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) vs) =
      Some (Some (map LPCAtom ts))"
  shows "lp_cut_guard_holds (lp_cut_guard_subst (lp_cut_instance_subst (zip vs ts)) g) \<eta> =
    lp_cut_guard_holds g \<eta>"
  by (simp add: lp_cut_guard_subst_holds lp_cut_normalized_interface_valuation[OF equations checked])

definition lp_cut_check_interface where
  "lp_cut_check_interface fuel eqs vs ts s G guards t H guards' =
    (lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) vs) =
       Some (Some (map LPCAtom ts)) \<and>
     t=lp_cut_state_map (\<lambda>u. u\<cdot>lp_cut_instance_subst (zip vs ts)) s \<and>
     set H \<subseteq> \<Union>(vars_term ` (lp_cut_instance_subst (zip vs ts) ` set G)) \<and>
     set guards' \<subseteq> set (map (lp_cut_guard_subst (lp_cut_instance_subst (zip vs ts))) guards))"

theorem lp_cut_checked_interface_state:
  assumes "lp_cut_check_interface fuel eqs vs ts s G guards t H guards'"
    "lp_equations eqs \<eta>"
  shows "lp_cut_state_eval t \<eta> = lp_cut_state_eval s \<eta>"
  using assms lp_cut_normalized_interface_state[of eqs \<eta> fuel vs ts s]
  by (auto simp: lp_cut_check_interface_def)

theorem lp_cut_checked_interface_knowledge:
  assumes checked: "lp_cut_check_interface fuel eqs vs ts s G guards t H guards'"
    and equations: "lp_equations eqs \<eta>"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
  shows "lp_cut_knowledge (set H) guards' \<eta>"
proof -
  let ?mu = "lp_cut_instance_subst (zip vs ts)"
  have norm: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) vs) =
      Some (Some (map LPCAtom ts))"
    using checked by (simp add: lp_cut_check_interface_def)
  have same: "\<And>x. lp_ieval (?mu x) \<eta> = \<eta> x"
    by (rule lp_cut_normalized_interface_valuation[OF equations norm])
  have interpreted: "\<forall>x\<in>set G. lp_seg_ground (lp_ieval (?mu x) \<eta>)"
    using knowledge by (simp add: same lp_cut_knowledge_def)
  have variables: "\<forall>x\<in>set G. \<forall>y\<in>vars_term (?mu x). lp_seg_ground (\<eta> y)"
    using interpreted by (simp add: lp_seg_ground_eval)
  have ground: "\<forall>x\<in>set H. lp_seg_ground (\<eta> x)"
    using checked variables by (auto simp: lp_cut_check_interface_def)
  have guards: "\<And>g. g\<in>set guards' \<Longrightarrow> lp_cut_guard_holds g \<eta>"
  proof -
    fix g assume member: "g\<in>set guards'"
    obtain h where h: "h\<in>set guards" and g: "g=lp_cut_guard_subst ?mu h"
      using checked member by (auto simp: lp_cut_check_interface_def)
    have "lp_cut_guard_holds h \<eta>"
      using knowledge h by (auto simp: lp_cut_knowledge_def list_all_iff)
    then show "lp_cut_guard_holds g \<eta>"
      by (simp add: g lp_cut_guard_subst_holds same)
  qed
  show ?thesis using ground guards by (auto simp: lp_cut_knowledge_def list_all_iff)
qed

end
