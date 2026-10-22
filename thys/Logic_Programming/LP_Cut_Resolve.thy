theory LP_Cut_Resolve
  imports LP_Cut_State
begin

fun lp_cut_terms where
  "lp_cut_terms (LPCAtom a) = [a]"
| "lp_cut_terms (LPCMeta a) = [a]"
| "lp_cut_terms (LPCExpand a m) = [a]"
| "lp_cut_terms (LPCUnify a b) = [a,b]"
| "lp_cut_terms _ = []"

definition lp_cut_short_goals where
  "lp_cut_short_goals k gs =
    (\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t. length x<k)"

fun lp_cut_short_entry where
  "lp_cut_short_entry k (LPCGoals gs) = lp_cut_short_goals k gs"
| "lp_cut_short_entry k (LPCClause gs c m) = lp_cut_short_goals k gs"
| "lp_cut_short_entry k (LPCBarrier m) = True"

definition lp_cut_resolution_env where
  "lp_cut_resolution_env k l \<eta> \<sigma> \<rho> x =
    (if l\<le>length x then \<rho> (drop l x)
     else if length x<k then \<eta> x else lp_isubst (\<eta> (drop k x)) \<sigma>)"

lemma lp_cut_resolution_old:
  assumes short: "\<forall>x\<in>vars_term t. length x<k" and bounds: "k\<le>l"
  shows "lp_ieval t (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) = lp_ieval t \<eta>"
  by (rule lp_ieval_cong) (use short bounds in \<open>auto simp: lp_cut_resolution_env_def\<close>)

lemma lp_cut_resolution_clause:
  "lp_ieval (t\<cdot>(\<lambda>x. Var (lp_prefix l x))) (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) =
    lp_ieval t \<rho>"
  by (simp add: lp_ieval_finite_subst lp_cut_resolution_env_def lp_prefix_def)

lemma lp_cut_resolution_active:
  assumes short: "\<forall>x\<in>vars_term t. length x<k" and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
  shows "lp_ieval (t\<cdot>lp_cut_refresh k G) (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) =
    lp_isubst (lp_ieval t \<eta>) \<sigma>"
  using short
proof (induct t)
  case (Var x)
  have old: "length x<k" using Var by simp
  have upper: "k+length x<l" and old_upper: "length x<l" using old bounds by arith+
  show ?case using old upper old_upper ground
    by (auto simp: lp_cut_refresh_def lp_cut_resolution_env_def lp_prefix_def lp_seg_ground_subst)
next
  case (Fun f ts)
  show ?case using Fun by (auto intro!: map_cong)
qed

lemma lp_cut_goal_map_cong:
  "(\<And>t. t\<in>set (lp_cut_terms g) \<Longrightarrow> f t=h t) \<Longrightarrow> lp_cut_map f g=lp_cut_map h g"
  by (cases g) auto

lemma lp_cut_resolution_saved_goals:
  assumes "lp_cut_short_goals k gs" "k\<le>l"
  shows "map (lp_cut_map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>))) gs =
    map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) gs"
  by (rule map_cong[OF refl], rule lp_cut_goal_map_cong, rule lp_cut_resolution_old)
    (use assms in \<open>auto simp: lp_cut_short_goals_def\<close>)

lemma lp_cut_resolution_saved_entry:
  assumes "lp_cut_short_entry k e" "k\<le>l"
  shows "lp_cut_entry_map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>)) e =
    lp_cut_entry_map (\<lambda>t. lp_ieval t \<eta>) e"
  using assms by (cases e) (auto simp: lp_cut_resolution_saved_goals)

lemma lp_cut_resolution_saved_stack:
  assumes "\<forall>e\<in>set es. lp_cut_short_entry k e" "k\<le>l"
  shows "lp_cut_state_eval es (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) = lp_cut_state_eval es \<eta>"
  unfolding lp_cut_state_map_def
  by (rule map_cong[OF refl], rule lp_cut_resolution_saved_entry) (use assms in auto)

lemma lp_cut_resolution_active_goals:
  assumes "lp_cut_short_goals k gs" "2 * k \<le> l" "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
  shows "map (lp_cut_map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>)))
      (map (lp_cut_map (\<lambda>t. t\<cdot>lp_cut_refresh k G)) gs) =
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs"
  unfolding map_map lp_cut_map_comp o_def
  by (rule map_cong[OF refl], rule lp_cut_goal_map_cong, rule lp_cut_resolution_active)
    (use assms in \<open>auto simp: lp_cut_short_goals_def\<close>)

lemma lp_cut_map_bind:
  "lp_cut_map f (lp_cut_bind m g a) = lp_cut_bind m (\<lambda>x. f (g x)) a"
  by (cases a) simp_all

text \<open>The checked normalizer represents every successful source unifier,
not just the particular unifier selected during native search. Saved choices
retain the incoming valuation. This theorem does not omit the failure branch;
its coverage is checked separately.\<close>

theorem lp_cut_normalized_resolution_covers_success:
  assumes short_call: "\<forall>x\<in>vars_term a. length x<k"
    and short_goals: "lp_cut_short_goals k gs"
    and short_saved: "\<forall>e\<in>set es. lp_cut_short_entry k e"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
    and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>"
    and checked: "lp_cut_normalize fuel
      [(a\<cdot>lp_cut_refresh k G,h\<cdot>(\<lambda>x. Var (lp_prefix l x)))]
      (map (lp_cut_bind m (\<lambda>t. t\<cdot>(\<lambda>x. Var (lp_prefix l x)))) body @
       map (lp_cut_map (\<lambda>t. t\<cdot>lp_cut_refresh k G)) gs) = Some (Some next)"
  shows "lp_cut_state_eval (LPCGoals next#es) (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) =
    LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) body @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs) # lp_cut_state_eval es \<eta>"
proof -
  let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<rho>"
  have kl: "k\<le>l" using bounds by arith
  have equations: "lp_equations
      [(a\<cdot>lp_cut_refresh k G,h\<cdot>(\<lambda>x. Var (lp_prefix l x)))] ?env"
    using unifier lp_cut_resolution_active[OF short_call bounds ground]
    by (simp add: lp_equations_def lp_cut_resolution_clause)
  have evaluated: "map (lp_cut_map (\<lambda>t. lp_ieval t ?env)) next =
      map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) body @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs"
    using lp_cut_normalize_success[OF checked equations]
      lp_cut_resolution_active_goals[OF short_goals bounds ground]
    by (simp add: map_map o_def lp_cut_map_bind lp_cut_resolution_clause)
  show ?thesis using evaluated lp_cut_resolution_saved_stack[OF short_saved kl]
    by (simp add: lp_cut_state_map_def)
qed

end
