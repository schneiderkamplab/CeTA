theory LP_Cut_Scope_Source
  imports LP_Cut_Allocate
begin

fun lp_cut_source_goal where
  "lp_cut_source_goal (LPCExpand a m) = False"
| "lp_cut_source_goal g = True"

definition lp_cut_source_program where
  "lp_cut_source_program P = (\<forall>c\<in>set P. list_all lp_cut_source_goal (snd c))"

lemma lp_cut_scope_goal_scopes:
  "lp_cut_goal_scopes (lp_cut_scope_goal r g) = r ` lp_cut_goal_scopes g"
  by (cases g) simp_all

lemma lp_cut_scope_entry_scopes:
  "lp_cut_entry_scopes (lp_cut_scope_entry r e) = r ` lp_cut_entry_scopes e"
  by (cases e) (auto simp: lp_cut_scope_goal_scopes)

lemma lp_cut_scope_fresh:
  "inj r \<Longrightarrow> lp_cut_fresh (r m) (map (lp_cut_scope_entry r) es) = lp_cut_fresh m es"
  by (auto simp: lp_cut_fresh_def lp_cut_scope_entry_scopes inj_eq)

lemma lp_cut_scope_bind:
  "lp_cut_source_goal g \<Longrightarrow>
    lp_cut_scope_goal r (lp_cut_bind m f g) = lp_cut_bind (r m) f g"
  by (cases g) simp_all

lemma lp_cut_scope_source:
  assumes step: "(s,t)\<in>lp_cut_source P"
    and injective: "inj r" and program: "lp_cut_source_program P"
  shows "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>lp_cut_source P"
  using step
proof (induct rule: lp_cut_source.induct)
  case (admin s t)
  show ?case by (rule lp_cut_source.admin)
    (simp add: lp_cut_scope_admin[OF injective] admin)
next
  case (case_call m f ts gs es)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) es)"
    using case_call(1) lp_cut_scope_fresh[OF injective, of m
      "LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es"] by simp
  show ?case using lp_cut_source.case_call[OF fresh]
    by (simp add: case_call map_map o_def)
next
  case (resolve c a \<sigma> \<rho> gs m es)
  have body: "map (lp_cut_scope_goal r)
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c))) =
    map (lp_cut_bind (r m) (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c))"
    using program resolve(1)
    by (auto simp: lp_cut_source_program_def list_all_iff map_map o_def
      intro!: map_cong lp_cut_scope_bind)
  show ?case using lp_cut_source.resolve[OF resolve(1,2), of "map (lp_cut_scope_goal r) gs" "r m"
      "map (lp_cut_scope_entry r) es"]
    by (simp add: resolve body[unfolded map_map o_def] map_map o_def lp_cut_scope_goal_map)
next
  case (backtrack c a gs m es)
  show ?case using lp_cut_source.backtrack[OF backtrack(1,2),
    of "map (lp_cut_scope_goal r) gs" "r m" "map (lp_cut_scope_entry r) es"]
    by (simp add: backtrack)
next
  case (unify a \<sigma> b gs es)
  show ?case using lp_cut_source.unify[OF unify(1), of "map (lp_cut_scope_goal r) gs"
      "map (lp_cut_scope_entry r) es"]
    by (simp add: unify map_map o_def lp_cut_scope_goal_map)
next
  case (unify_fail a b gs es)
  show ?case using lp_cut_source.unify_fail[OF unify_fail(1), of "map (lp_cut_scope_goal r) gs"
      "map (lp_cut_scope_entry r) es"]
    by (simp add: unify_fail)
next
  case (meta m a gs es body)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCMeta a#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) es)"
    using meta(1) lp_cut_scope_fresh[OF injective, of m "LPCGoals (LPCMeta a#gs)#es"] by simp
  show ?case using lp_cut_source.meta[OF fresh lp_cut_scope_lower[OF meta(2), of r]]
    by (simp add: meta)
next
  case (meta_unlowerable a gs es)
  show ?case using lp_cut_source.meta_unlowerable[OF meta_unlowerable(1),
    of "map (lp_cut_scope_goal r) gs" "map (lp_cut_scope_entry r) es"]
    by (simp add: meta_unlowerable)
qed

lemma lp_cut_scope_goal_comp:
  "lp_cut_scope_goal r (lp_cut_scope_goal q g) = lp_cut_scope_goal (r\<circ>q) g"
  by (cases g) simp_all

lemma lp_cut_scope_entry_comp:
  "lp_cut_scope_entry r (lp_cut_scope_entry q e) = lp_cut_scope_entry (r\<circ>q) e"
  by (cases e) (simp_all add: map_map o_def lp_cut_scope_goal_comp)

lemma lp_cut_scope_identity:
  "map (lp_cut_scope_entry id) es=es"
  by (induct es) (auto intro!: lp_cut_scope_entry_fixed)

lemma lp_cut_scope_reflects_SN:
  assumes injective: "inj r" and program: "lp_cut_source_program P"
    and sn: "SN_on (lp_cut_source P) {map (lp_cut_scope_entry r) s}"
  shows "SN_on (lp_cut_source P) {s}"
proof -
  have all: "\<forall>s. xs=map (lp_cut_scope_entry r) s \<longrightarrow> SN_on (lp_cut_source P) {s}"
    if "SN_on (lp_cut_source P) {xs}" for xs
  proof (rule SN_on_induct[OF that singletonI], intro allI impI)
    fix xs s
    assume ih: "\<And>ys. (xs,ys)\<in>lp_cut_source P \<Longrightarrow>
      \<forall>s. ys=map (lp_cut_scope_entry r) s \<longrightarrow> SN_on (lp_cut_source P) {s}"
      and represented: "xs=map (lp_cut_scope_entry r) s"
    show "SN_on (lp_cut_source P) {s}"
    proof (rule step_reflects_SN_on)
      fix t assume step: "(s,t)\<in>lp_cut_source P"
      show "SN_on (lp_cut_source P) {t}"
        using ih[OF lp_cut_scope_source[OF step injective program, folded represented]] by blast
    qed
  qed
  show ?thesis using all[OF sn] by blast
qed

lemma lp_cut_scope_swap_preserves_SN:
  assumes "lp_cut_source_program P" "SN_on (lp_cut_source P) {s}"
  shows "SN_on (lp_cut_source P) {map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s}"
proof -
  have twice: "map (lp_cut_scope_entry (lp_cut_scope_swap a b))
    (map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s)=s"
    by (simp add: map_map o_def lp_cut_scope_entry_comp lp_cut_scope_swap_inverse
      lp_cut_scope_identity[unfolded id_def])
  show ?thesis by (rule lp_cut_scope_reflects_SN[OF lp_cut_scope_swap_injective[of a b] assms(1)])
    (use assms(2) twice in simp)
qed

end
