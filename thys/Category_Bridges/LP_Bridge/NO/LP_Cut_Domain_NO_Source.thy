theory LP_Cut_Domain_NO_Source
  imports LP_Cut_Domain_MGU
begin

text \<open>The witness relation uses domain-specific MGUs and admits only
function-root meta-calls. Checked failures have no unrestricted-tree solution,
which also establishes failure in each smaller domain.\<close>

context cut_runtime_domain
begin

inductive_set mgu_source ::
  "('f,string) lp_cut_program \<Rightarrow>
   ('f lp_cut_symbol,string) lp_iterm lp_cut_entry list rel"
  for P where
  admin: "lp_cut_admin s = Some t \<Longrightarrow> (s,t) \<in> mgu_source P"
| case_call: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es) \<Longrightarrow>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,
     map (\<lambda>c. LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m)
       (lp_cut_slice P (LPCUser f) (length ts)) @ LPCBarrier m # es) \<in> mgu_source P"
| resolve: "c<length P \<Longrightarrow> mgu_resolve a gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<Longrightarrow>
    (LPCClause (LPCAtom a#gs) c m # es,
     LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs) # es) \<in> mgu_source P"
| backtrack: "c<length P \<Longrightarrow> \<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>) \<Longrightarrow>
    (LPCClause (LPCAtom a#gs) c m # es, es) \<in> mgu_source P"
| unify: "mgu_unify a b gs \<sigma> \<Longrightarrow>
    (LPCGoals (LPCUnify a b#gs)#es,
     LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)#es) \<in> mgu_source P"
| unify_fail: "\<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      lp_isubst a \<sigma> = lp_isubst b \<sigma>) \<Longrightarrow>
    (LPCGoals (LPCUnify a b#gs)#es, es) \<in> mgu_source P"
| meta: "lp_cut_fresh m (LPCGoals (LPCMeta a#gs)#es) \<Longrightarrow>
    lp_cut_lower m a body \<Longrightarrow> (\<exists>f ts. a=LPIFun f ts) \<Longrightarrow>
    (LPCGoals (LPCMeta a#gs)#es,
     LPCGoals (body@gs)#LPCBarrier m#es) \<in> mgu_source P"
lemma scoped_goal_maps:
  assumes eq: "map (lp_cut_map f) gs = map (lp_cut_map g) gs"
  shows "map (lp_cut_map f) (map (lp_cut_scope_goal r) gs) =
   map (lp_cut_map g) (map (lp_cut_scope_goal r) gs)"
  using arg_cong[OF eq, of "map (lp_cut_scope_goal r)"]
  by (simp only: map_map o_def lp_cut_scope_goal_map)

lemma mgu_resolve_scope:
  "mgu_resolve a gs h bs sigma rho \<Longrightarrow>
   mgu_resolve a (map (lp_cut_scope_goal r) gs) h bs sigma rho"
  unfolding mgu_resolve_def by (meson scoped_goal_maps)

lemma mgu_unify_scope:
  "mgu_unify a b gs sigma \<Longrightarrow>
   mgu_unify a b (map (lp_cut_scope_goal r) gs) sigma"
  unfolding mgu_unify_def by (meson scoped_goal_maps)

lemma mgu_scope_source:
  assumes step: "(s,t)\<in>mgu_source P"
    and injective: "inj r" and program: "lp_cut_source_program P"
  shows "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>mgu_source P"
  using step
proof (induct rule: mgu_source.induct)
  case (admin s t)
  show ?case by (rule mgu_source.admin)
    (simp add: lp_cut_scope_admin[OF injective] admin)
next
  case (case_call m f ts gs es)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) es)"
    using case_call(1) lp_cut_scope_fresh[OF injective, of m
      "LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es"] by simp
  show ?case using mgu_source.case_call[OF fresh]
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
  show ?case using mgu_source.resolve[OF resolve(1) mgu, of "r m" "map (lp_cut_scope_entry r) es"]
    by (simp add: resolve body[unfolded map_map o_def] map_map o_def lp_cut_scope_goal_map)
next
  case (backtrack c a gs m es)
  show ?case using mgu_source.backtrack[OF backtrack(1,2),
    of "map (lp_cut_scope_goal r) gs" "r m" "map (lp_cut_scope_entry r) es"]
    by (simp add: backtrack)
next
  case (unify a b gs \<sigma> es)
  have mgu: "mgu_unify a b (map (lp_cut_scope_goal r) gs) \<sigma>"
    by (rule mgu_unify_scope[OF unify(1)])
  show ?case using mgu_source.unify[OF mgu, of "map (lp_cut_scope_entry r) es"]
    by (simp add: unify map_map o_def lp_cut_scope_goal_map)
next
  case (unify_fail a b gs es)
  show ?case using mgu_source.unify_fail[OF unify_fail(1), of "map (lp_cut_scope_goal r) gs"
      "map (lp_cut_scope_entry r) es"]
    by (simp add: unify_fail)
next
  case (meta m a gs es body)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCMeta a#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) es)"
    using meta(1) lp_cut_scope_fresh[OF injective, of m "LPCGoals (LPCMeta a#gs)#es"] by simp
  show ?case using mgu_source.meta[OF fresh lp_cut_scope_lower[OF meta(2), of r] meta(3)]
    by (simp add: meta)
qed

end
end
