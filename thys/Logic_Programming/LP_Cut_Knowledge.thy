theory LP_Cut_Knowledge
  imports LP_Cut_Resolve
begin

datatype 'f lp_cut_guard =
    LPCHeadGuard "('f,string) term" "('f,string) term" bool
  | LPCEqGuard "('f,string) term" "('f,string) term" bool

fun lp_cut_guard_holds ::
  "'f lp_cut_guard \<Rightarrow> (string \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow> bool" where
  "lp_cut_guard_holds (LPCHeadGuard a h b) \<eta> =
    ((\<exists>\<sigma>::string\<Rightarrow>('f,string) lp_iterm. \<exists>\<rho>.
       lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>) = b)"
| "lp_cut_guard_holds (LPCEqGuard a c b) \<eta> =
    ((\<exists>\<sigma>::string\<Rightarrow>('f,string) lp_iterm.
       lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval c \<eta>) \<sigma>) = b)"

fun lp_cut_short_guard where
  "lp_cut_short_guard k (LPCHeadGuard a h b) = (\<forall>x\<in>vars_term a. length x<k)"
| "lp_cut_short_guard k (LPCEqGuard a c b) =
    (\<forall>x\<in>vars_term a \<union> vars_term c. length x<k)"

definition lp_cut_knowledge where
  "lp_cut_knowledge G guards \<eta> =
    ((\<forall>x\<in>G. lp_seg_ground (\<eta> x)) \<and> list_all (\<lambda>g. lp_cut_guard_holds g \<eta>) guards)"

lemma lp_cut_resolution_guard_preserved:
  assumes "lp_cut_short_guard k g" "k\<le>l"
  shows "lp_cut_guard_holds g (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) =
    lp_cut_guard_holds g \<eta>"
  using assms by (cases g) (auto simp: lp_cut_resolution_old)

lemma lp_cut_resolution_knowledge_preserved:
  assumes "lp_cut_knowledge G guards \<eta>"
    "\<forall>x\<in>G. length x<k" "\<forall>g\<in>set guards. lp_cut_short_guard k g" "k\<le>l"
  shows "lp_cut_knowledge G guards (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>)"
  using assms lp_cut_resolution_guard_preserved[of k _ l \<eta> \<sigma> \<rho>]
  by (auto simp: lp_cut_knowledge_def lp_cut_resolution_env_def list_all_iff)

lemma lp_cut_resolution_positive_guard:
  fixes \<eta> :: "string\<Rightarrow>('f,string) lp_iterm"
  assumes "\<forall>x\<in>vars_term a. length x<k" "k\<le>l"
    "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>"
  shows "lp_cut_guard_holds (LPCHeadGuard a h True) (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>)"
  using assms lp_cut_resolution_old[OF assms(1,2), of \<eta> \<sigma> \<rho>]
  by auto

text \<open>Groundness of normalized anchor terms establishes groundness of
their variables. Anchors are normalized by the same equations as the active
successor; the checker must not accept an arbitrary claimed ground-variable set.\<close>

lemma lp_cut_normalized_terms:
  assumes equations: "lp_equations eqs \<eta>"
    and checked: "lp_cut_normalize fuel eqs (map LPCAtom ts) = Some (Some (map LPCAtom us))"
  shows "map (\<lambda>t. lp_ieval t \<eta>) us = map (\<lambda>t. lp_ieval t \<eta>) ts"
proof -
  have evaluated: "map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) (map LPCAtom us) =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) (map LPCAtom ts)"
    by (rule lp_cut_normalize_success[OF checked equations])
  show ?thesis
    using arg_cong[OF evaluated, of "\<lambda>gs. concat (map lp_cut_terms gs)"]
    by (simp add: map_map o_def)
qed

theorem lp_cut_normalized_anchors_ground:
  assumes equations: "lp_equations eqs \<eta>"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
    and checked: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) G) =
      Some (Some (map LPCAtom anchors))"
  shows "\<forall>a\<in>set anchors. \<forall>x\<in>vars_term a. lp_seg_ground (\<eta> x)"
proof -
  have terms: "map (\<lambda>t. lp_ieval t \<eta>) anchors = map \<eta> G"
    using lp_cut_normalized_terms[OF equations, of fuel "map Var G" anchors] checked
    by (simp add: map_map o_def)
  have old: "list_all lp_seg_ground (map \<eta> G)"
    using ground by (simp add: list_all_iff)
  have "list_all lp_seg_ground (map (\<lambda>t. lp_ieval t \<eta>) anchors)"
    using old terms by simp
  then have "\<forall>a\<in>set anchors. lp_seg_ground (lp_ieval a \<eta>)"
    by (simp add: list_all_iff)
  then show ?thesis by (simp only: lp_seg_ground_eval)
qed

end
