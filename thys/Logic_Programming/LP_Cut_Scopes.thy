theory LP_Cut_Scopes
  imports LP_Cut_State
begin

text \<open>Scope identifiers are administrative names, not source data.
Two fresh choices are interchangeable by a bijection fixing every live scope.
This does not restrict the source semantics to the allocator used by search.\<close>

fun lp_cut_scope_goal where
  "lp_cut_scope_goal r (LPCCut m) = LPCCut (r m)"
| "lp_cut_scope_goal r (LPCExpand a m) = LPCExpand a (r m)"
| "lp_cut_scope_goal r g = g"

fun lp_cut_scope_entry where
  "lp_cut_scope_entry r (LPCGoals gs) = LPCGoals (map (lp_cut_scope_goal r) gs)"
| "lp_cut_scope_entry r (LPCClause gs c m) =
    LPCClause (map (lp_cut_scope_goal r) gs) c (r m)"
| "lp_cut_scope_entry r (LPCBarrier m) = LPCBarrier (r m)"

definition lp_cut_scope_swap where
  "lp_cut_scope_swap a b x = (if x=a then b else if x=b then a else x)"

lemma lp_cut_scope_swap_inverse:
  "lp_cut_scope_swap a b (lp_cut_scope_swap a b x) = x"
  by (auto simp: lp_cut_scope_swap_def)

lemma lp_cut_scope_swap_injective:
  "inj (lp_cut_scope_swap a b)"
  by (rule injI) (metis lp_cut_scope_swap_inverse)

lemma lp_cut_scope_goal_fixed:
  "(\<And>m. m\<in>lp_cut_goal_scopes g \<Longrightarrow> r m=m) \<Longrightarrow>
    lp_cut_scope_goal r g=g"
  by (cases g) auto

lemma lp_cut_scope_entry_fixed:
  "(\<And>m. m\<in>lp_cut_entry_scopes e \<Longrightarrow> r m=m) \<Longrightarrow>
    lp_cut_scope_entry r e=e"
  by (cases e) (auto intro!: map_idI lp_cut_scope_goal_fixed)

lemma lp_cut_fresh_swap_fixes:
  assumes "lp_cut_fresh a es" "lp_cut_fresh b es"
  shows "map (lp_cut_scope_entry (lp_cut_scope_swap a b)) es = es"
  using assms unfolding lp_cut_fresh_def
  by (intro map_idI lp_cut_scope_entry_fixed) (auto simp: lp_cut_scope_swap_def)

lemma lp_cut_scope_prune:
  assumes "inj r"
  shows "map (lp_cut_scope_entry r) (lp_cut_prune m es) =
    lp_cut_prune (r m) (map (lp_cut_scope_entry r) es)"
  using assms by (induct es) (auto simp: inj_eq split: lp_cut_entry.splits)

lemma lp_cut_scope_goal_map:
  "lp_cut_scope_goal r (lp_cut_map f g) = lp_cut_map f (lp_cut_scope_goal r g)"
  by (cases g) simp_all

lemma lp_cut_scope_admin:
  assumes "inj r"
  shows "lp_cut_admin (map (lp_cut_scope_entry r) es) =
    map_option (map (lp_cut_scope_entry r)) (lp_cut_admin es)"
proof (induct es rule: lp_cut_admin.induct)
  case (5 g gs es)
  then show ?case by (cases g) (simp_all add: lp_cut_scope_prune[OF assms])
qed simp_all

lemma lp_cut_fresh_swap_call:
  assumes fresh_a: "lp_cut_fresh a (LPCGoals (LPCAtom t#gs)#es)"
    and fresh_b: "lp_cut_fresh b (LPCGoals (LPCAtom t#gs)#es)"
  shows "map (lp_cut_scope_entry (lp_cut_scope_swap a b))
      (map (\<lambda>c. LPCClause (LPCAtom t#gs) c a) cs @ LPCBarrier a#es) =
    map (\<lambda>c. LPCClause (LPCAtom t#gs) c b) cs @ LPCBarrier b#es"
proof -
  have fixed: "map (lp_cut_scope_entry (lp_cut_scope_swap a b))
      (LPCGoals (LPCAtom t#gs)#es) = LPCGoals (LPCAtom t#gs)#es"
    by (rule lp_cut_fresh_swap_fixes[OF fresh_a fresh_b])
  then have goals: "map (lp_cut_scope_goal (lp_cut_scope_swap a b)) gs=gs"
    and tail: "map (lp_cut_scope_entry (lp_cut_scope_swap a b)) es=es"
    by simp_all
  show ?thesis by (simp add: map_map goals tail lp_cut_scope_swap_def)
qed

lemma lp_cut_scope_lower:
  "lp_cut_lower m t body \<Longrightarrow>
    lp_cut_lower (r m) t (map (lp_cut_scope_goal r) body)"
  by (induct rule: lp_cut_lower.induct)
    (auto intro: lp_cut_lower.intros)

lemma lp_cut_fresh_swap_meta:
  assumes fresh_a: "lp_cut_fresh a (LPCGoals (LPCMeta t#gs)#es)"
    and fresh_b: "lp_cut_fresh b (LPCGoals (LPCMeta t#gs)#es)"
    and lower_a: "lp_cut_lower a t body_a"
    and lower_b: "lp_cut_lower b t body_b"
  shows "map (lp_cut_scope_entry (lp_cut_scope_swap a b))
      (LPCGoals (body_a@gs)#LPCBarrier a#es) =
    LPCGoals (body_b@gs)#LPCBarrier b#es"
proof -
  have fixed: "map (lp_cut_scope_entry (lp_cut_scope_swap a b))
      (LPCGoals (LPCMeta t#gs)#es) = LPCGoals (LPCMeta t#gs)#es"
    by (rule lp_cut_fresh_swap_fixes[OF fresh_a fresh_b])
  then have goals: "map (lp_cut_scope_goal (lp_cut_scope_swap a b)) gs=gs"
    and tail: "map (lp_cut_scope_entry (lp_cut_scope_swap a b)) es=es"
    by simp_all
  have lowered: "lp_cut_lower b t
      (map (lp_cut_scope_goal (lp_cut_scope_swap a b)) body_a)"
    using lp_cut_scope_lower[OF lower_a, of "lp_cut_scope_swap a b"]
    by (simp add: lp_cut_scope_swap_def)
  have body: "map (lp_cut_scope_goal (lp_cut_scope_swap a b)) body_a=body_b"
    by (rule lp_cut_lower_deterministic[OF lowered lower_b])
  show ?thesis by (simp add: goals tail body lp_cut_scope_swap_def)
qed

end
