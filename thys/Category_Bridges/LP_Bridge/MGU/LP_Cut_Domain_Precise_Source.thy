theory LP_Cut_Domain_Precise_Source
  imports LP_Cut_Domain_MGU_Properties Category_LP_Cut_NO_Bridge.LP_Cut_Domain_NO_Source
begin

text \<open>The MGU-aware YES relation uses domain-specific success and failure.
Its malformed-meta overapproximation is conservative for termination. This is
separate from the witness relation, whose checked failures need only establish
the stronger absence of an unrestricted-tree solution.\<close>

context cut_runtime_domain
begin

inductive_set precise_source ::
  "('f,string) lp_cut_program \<Rightarrow>
   ('f lp_cut_symbol,string) lp_iterm lp_cut_entry list rel"
  for P where
  admin: "lp_cut_admin s = Some t \<Longrightarrow> (s,t) \<in> precise_source P"
| case_call: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es) \<Longrightarrow>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,
     map (\<lambda>c. LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m)
       (lp_cut_slice P (LPCUser f) (length ts)) @ LPCBarrier m # es) \<in> precise_source P"
| resolve: "c<length P \<Longrightarrow> mgu_resolve a gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<Longrightarrow>
    (LPCClause (LPCAtom a#gs) c m # es,
     LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs) # es) \<in> precise_source P"
| backtrack: "c<length P \<Longrightarrow> \<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>) \<Longrightarrow>
    (LPCClause (LPCAtom a#gs) c m # es, es) \<in> precise_source P"
| unify: "mgu_unify a b gs \<sigma> \<Longrightarrow>
    (LPCGoals (LPCUnify a b#gs)#es,
     LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)#es) \<in> precise_source P"
| unify_fail: "\<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and> lp_isubst a \<sigma> = lp_isubst b \<sigma>) \<Longrightarrow>
    (LPCGoals (LPCUnify a b#gs)#es, es) \<in> precise_source P"
| meta: "lp_cut_fresh m (LPCGoals (LPCMeta a#gs)#es) \<Longrightarrow>
    lp_cut_lower m a body \<Longrightarrow>
    (LPCGoals (LPCMeta a#gs)#es,
     LPCGoals (body@gs)#LPCBarrier m#es) \<in> precise_source P"
| meta_unlowerable:
    "\<not>(\<exists>m body. lp_cut_lower m a body) \<Longrightarrow>
     (LPCGoals (LPCMeta a#gs)#es, LPCGoals (LPCMeta a#gs)#es) \<in> precise_source P"

lemma precise_source_subset: "precise_source P \<subseteq> source P"
proof
  fix st assume "st \<in> precise_source P"
  moreover obtain s t where "st=(s,t)" by (cases st) auto
  ultimately have "(s,t)\<in>precise_source P" by simp
  then have "(s,t)\<in>source P"
  proof (induct rule: precise_source.induct)
    case (backtrack c a gs m es)
    show ?case by (rule source.backtrack[OF backtrack])
  next
    case (unify_fail a b gs es)
    show ?case by (rule source.unify_fail[OF unify_fail])
  qed (auto simp: mgu_resolve_def mgu_unify_def intro: source.intros)
  then show "st\<in>source P" using \<open>st=(s,t)\<close> by simp
qed

lemma conservative_implies_precise_SN:
  "SN_on (source P) S \<Longrightarrow> SN_on (precise_source P) S"
  by (rule SN_on_subset1) (auto intro: precise_source_subset[THEN subsetD])

lemma precise_scope_source:
  assumes step: "(s,t)\<in>precise_source P"
    and injective: "inj r" and program: "lp_cut_source_program P"
  shows "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>precise_source P"
  using step
proof (induct rule: precise_source.induct)
  case (admin s t)
  show ?case by (rule precise_source.admin)
    (simp add: lp_cut_scope_admin[OF injective] admin)
next
  case (case_call m f ts gs es)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) es)"
    using case_call(1) lp_cut_scope_fresh[OF injective, of m
      "LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es"] by simp
  show ?case using precise_source.case_call[OF fresh]
    by (simp add: case_call map_map o_def)
next
  case (resolve c a gs \<sigma> \<rho> m es)
  have body: "map (lp_cut_scope_goal r)
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c))) =
    map (lp_cut_bind (r m) (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c))"
    using program resolve(1)
    by (auto simp: lp_cut_source_program_def list_all_iff map_map o_def
      intro!: map_cong lp_cut_scope_bind)
  have mgu: "mgu_resolve a (map (lp_cut_scope_goal r) gs) (fst (P!c)) (snd (P!c)) \<sigma> \<rho>"
    by (rule mgu_resolve_scope[OF resolve(2)])
  show ?case using precise_source.resolve[OF resolve(1) mgu, of "r m" "map (lp_cut_scope_entry r) es"]
    by (simp add: resolve body[unfolded map_map o_def] map_map o_def lp_cut_scope_goal_map)
next
  case (backtrack c a gs m es)
  show ?case using precise_source.backtrack[OF backtrack(1,2),
    of "map (lp_cut_scope_goal r) gs" "r m" "map (lp_cut_scope_entry r) es"]
    by (simp add: backtrack)
next
  case (unify a b gs \<sigma> es)
  have mgu: "mgu_unify a b (map (lp_cut_scope_goal r) gs) \<sigma>"
    by (rule mgu_unify_scope[OF unify(1)])
  show ?case using precise_source.unify[OF mgu, of "map (lp_cut_scope_entry r) es"]
    by (simp add: unify map_map o_def lp_cut_scope_goal_map)
next
  case (unify_fail a b gs es)
  show ?case using precise_source.unify_fail[OF unify_fail(1), of "map (lp_cut_scope_goal r) gs"
      "map (lp_cut_scope_entry r) es"]
    by (simp add: unify_fail)
next
  case (meta m a gs es body)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCMeta a#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) es)"
    using meta(1) lp_cut_scope_fresh[OF injective, of m "LPCGoals (LPCMeta a#gs)#es"] by simp
  show ?case using precise_source.meta[OF fresh lp_cut_scope_lower[OF meta(2), of r]]
    by (simp add: meta)
next
  case (meta_unlowerable a gs es)
  show ?case using precise_source.meta_unlowerable[OF meta_unlowerable(1),
    of "map (lp_cut_scope_goal r) gs" "map (lp_cut_scope_entry r) es"]
    by (simp add: meta_unlowerable)
qed

lemma precise_scope_reflects_SN:
  assumes injective: "inj r" and program: "lp_cut_source_program P"
    and sn: "SN_on (precise_source P) {map (lp_cut_scope_entry r) s}"
  shows "SN_on (precise_source P) {s}"
proof -
  have all: "\<forall>s. xs=map (lp_cut_scope_entry r) s \<longrightarrow> SN_on (precise_source P) {s}"
    if "SN_on (precise_source P) {xs}" for xs
  proof (rule SN_on_induct[OF that singletonI], intro allI impI)
    fix xs s
    assume ih: "\<And>ys. (xs,ys)\<in>precise_source P \<Longrightarrow>
      \<forall>s. ys=map (lp_cut_scope_entry r) s \<longrightarrow> SN_on (precise_source P) {s}"
      and represented: "xs=map (lp_cut_scope_entry r) s"
    show "SN_on (precise_source P) {s}"
    proof (rule step_reflects_SN_on)
      fix t assume step: "(s,t)\<in>precise_source P"
      show "SN_on (precise_source P) {t}"
        using ih[OF precise_scope_source[OF step injective program, folded represented]] by blast
    qed
  qed
  show ?thesis using all[OF sn] by blast
qed

lemma precise_scope_swap_preserves_SN:
  assumes "lp_cut_source_program P" "SN_on (precise_source P) {s}"
  shows "SN_on (precise_source P) {map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s}"
proof -
  have twice: "map (lp_cut_scope_entry (lp_cut_scope_swap a b))
    (map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s)=s"
    by (simp add: map_map o_def lp_cut_scope_entry_comp lp_cut_scope_swap_inverse
      lp_cut_scope_identity[unfolded id_def])
  show ?thesis by (rule precise_scope_reflects_SN[OF lp_cut_scope_swap_injective[of a b] assms(1)])
    (use assms(2) twice in simp)
qed

end
end
