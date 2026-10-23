theory LP_Cut_MGU_Link
  imports LP_Cut_MGU_Instance LP_Cut_Table_Link
begin

fun lpc_free_goal_vars where
  "lpc_free_goal_vars [] = Some []"
| "lpc_free_goal_vars (LPCAtom (Var x)#gs) = map_option ((#) x) (lpc_free_goal_vars gs)"
| "lpc_free_goal_vars _ = None"

lemma lpc_free_goal_vars_sound:
  "lpc_free_goal_vars gs = Some xs \<Longrightarrow> gs=map (\<lambda>x. LPCAtom (Var x)) xs"
  by (induct gs arbitrary: xs rule: lpc_free_goal_vars.induct) (auto split: option.splits)

definition lpc_check_link_free where
  "lpc_check_link_free fuel equations F H bindings =
    (distinct H \<and>
      (case lp_cut_normalize fuel equations
        (map (\<lambda>x. LPCAtom (lp_cut_instance_subst bindings x)) H) of
       Some (Some gs) \<Rightarrow> (case lpc_free_goal_vars gs of
         Some xs \<Rightarrow> distinct xs \<and> set xs \<subseteq> set F
         | None \<Rightarrow> False)
       | _ \<Rightarrow> False))"

theorem lpc_checked_link_free_sound:
  assumes checked: "lpc_check_link_free fuel equations F H bindings"
    and equations: "lp_equations equations \<eta>"
    and known: "lpc_free_knowledge (set F) \<eta>"
  shows "lpc_free_knowledge (set H) (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>)"
proof -
  let ?mu = "lp_cut_instance_subst bindings"
  let ?nu = "\<lambda>x. lp_ieval (?mu x) \<eta>"
  obtain gs xs where normalized: "lp_cut_normalize fuel equations
      (map (\<lambda>x. LPCAtom (?mu x)) H) = Some (Some gs)"
    and extracted: "lpc_free_goal_vars gs = Some xs"
    and distinct: "distinct xs" and subset: "set xs \<subseteq> set F"
    using checked by (auto simp: lpc_check_link_free_def split: option.splits)
  have shape: "gs=map (\<lambda>x. LPCAtom (Var x)) xs" by (rule lpc_free_goal_vars_sound[OF extracted])
  have valuation_eq: "map \<eta> xs = map ?nu H"
    using lp_cut_normalized_terms[OF equations, of fuel "map ?mu H" "map Var xs"] normalized shape
    by (simp add: map_map o_def)
  have fresh: "list_all (\<lambda>t. \<exists>x. t=LPIVar x) (map \<eta> xs)"
    using known subset by (auto simp: lpc_free_knowledge_def list_all_iff)
  have free: "\<forall>x\<in>set H. \<exists>y. ?nu x=LPIVar y"
    using fresh by (simp add: valuation_eq list_all_iff)
  have injective: "inj_on \<eta> (set xs)"
    using known subset by (auto simp: lpc_free_knowledge_def inj_on_def)
  have "distinct (map \<eta> xs)" using distinct injective by (simp add: distinct_map)
  then have "distinct (map ?nu H)" by (simp only: valuation_eq)
  then have "inj_on ?nu (set H)" by (simp add: distinct_map)
  then show ?thesis using free by (simp add: lpc_free_knowledge_def)
qed

theorem lpc_mgu_link_sound:
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_link fuel Q nds nd s G K eqs e"
    and free_checked: "lpc_check_link_free fuel eqs F (Fs ! lpcl_target e) (lpcl_bindings e)"
    and equations: "lp_equations eqs \<eta>'"
    and old: "map \<eta>' (lpcn_vars nd)=map \<eta> (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K \<eta>'"
    and free: "lpc_free_knowledge (set F) \<eta>'"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval s \<eta>'}"
proof -
  let ?child = "nds ! lpcl_target e"
  let ?mu = "lp_cut_instance_subst (lpcl_bindings e)"
  let ?nu = "\<lambda>x. lp_ieval (?mu x) \<eta>'"
  have bound: "lpcl_target e<length nds"
    and intf: "lp_cut_check_interface fuel eqs (lpcl_vars e) (lpcl_terms e) s G K
      (lpcl_state e) (lpcl_ground e) (lpcl_guards e)"
    and inst: "lp_cut_check_instance (lpcl_state e) (lpcl_ground e) (lpcl_guards e)
      (lpcn_state ?child) (lpcn_ground ?child) (lpcn_guards ?child)
      (lpcl_bindings e) (lpcl_swaps e)"
    and inputs: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcn_vars nd)) =
      Some (Some (map LPCAtom (lpcl_lhs e)))"
    and outputs: "lp_cut_normalize fuel eqs (map LPCAtom (map ?mu (lpcn_vars ?child))) =
      Some (Some (map LPCAtom (lpcl_rhs e)))"
    and clause: "((lpcn_pred nd,lpcl_lhs e),[(lpcn_pred ?child,lpcl_rhs e)]) \<in> set Q"
    using checked by (auto simp: lpc_check_link_def Let_def)
  have specialized: "lp_cut_knowledge (set (lpcl_ground e)) (lpcl_guards e) \<eta>'"
    by (rule lp_cut_checked_interface_knowledge[OF intf equations known])
  have child_known: "lp_cut_knowledge (set (lpcn_ground ?child)) (lpcn_guards ?child) ?nu"
    by (rule lp_cut_checked_instance_knowledge[OF inst specialized])
  have child_free: "lpc_free_knowledge (set (Fs ! lpcl_target e)) ?nu"
    by (rule lpc_checked_link_free_sound[OF free_checked equations free])
  have rhs: "map (\<lambda>t. lp_ieval t \<eta>') (lpcl_rhs e)=map ?nu (lpcn_vars ?child)"
    using lp_cut_normalized_terms[OF equations outputs] by (simp add: map_map o_def)
  have edge: "([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
      [(lpcn_pred ?child,map ?nu (lpcn_vars ?child))]) \<in> lp_ild Q"
    using lp_cut_normalized_residual_step[OF clause equations inputs old] rhs by simp
  have child_sn: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state ?child) ?nu}"
    by (rule ih[OF bound child_known child_free edge])
  have specialized_sn: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcl_state e) \<eta>'}"
    by (rule lpc_mgu_checked_instance_SN[OF program inst child_sn])
  show ?thesis using specialized_sn lp_cut_checked_interface_state[OF intf equations] by simp
qed

lemma lpc_mgu_plain_link_sound:
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_link fuel Q nds nd s G K [] e"
    and free_checked: "lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e)"
    and known: "lp_cut_knowledge (set G) K \<eta>"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval s \<eta>}"
  by (rule lpc_mgu_link_sound[OF program checked free_checked _ refl known free ih])
    (simp add: lp_equations_def)

text \<open>Knowledge is checked through the actual normalized child interface.
A raw variable-name match is not sufficient: an instance link may alias or
instantiate variables, and either operation can invalidate the child's claimed
free-variable block.\<close>

end
