theory LP_Cut_Equality
  imports LP_Cut_Knowledge LP_Cut_Failure
begin

text \<open>Built-in equality uses one active namespace for both operands.
Unlike clause resolution, neither operand is a freshly renamed clause head.
Unknown active values may change while saved alternatives keep their values.\<close>

definition lp_cut_check_unify where
  "lp_cut_check_unify fuel k l G guards a b gs es next =
    (2 * k \<le> l \<and>
     (\<forall>x\<in>vars_term a \<union> vars_term b. length x<k) \<and>
     lp_cut_short_goals k gs \<and> (\<forall>e\<in>set es. lp_cut_short_entry k e) \<and>
     (\<forall>x\<in>set G. length x<k) \<and>
     (\<forall>g\<in>set guards. lp_cut_short_guard k g) \<and>
     lp_cut_normalize fuel [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))]
       (map (lp_cut_map (\<lambda>t. t\<cdot>lp_cut_refresh k (set G))) gs) = Some (Some next))"

theorem lp_cut_checked_unify_success:
  fixes \<eta> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lp_cut_check_unify fuel k l G guards a b gs es next"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
    and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
  defines "\<eta>' \<equiv> lp_cut_resolution_env k l \<eta> \<sigma> \<eta>"
  shows "lp_cut_state_eval (LPCGoals next#es) \<eta>' =
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs)#lp_cut_state_eval es \<eta>"
    and "lp_cut_knowledge (set G) (guards@[LPCEqGuard a b True]) \<eta>'"
proof -
  have short_a: "\<forall>x\<in>vars_term a. length x<k"
    and short_b: "\<forall>x\<in>vars_term b. length x<k"
    and goals: "lp_cut_short_goals k gs"
    and saved: "\<forall>e\<in>set es. lp_cut_short_entry k e"
    and bounds: "2 * k \<le> l"
    using checked by (auto simp: lp_cut_check_unify_def)
  have kl: "k\<le>l" using bounds by arith
  have ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
    using knowledge by (simp add: lp_cut_knowledge_def)
  have equations: "lp_equations
      [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))] \<eta>'"
    using unifier lp_cut_resolution_active[OF short_a bounds ground]
      lp_cut_resolution_active[OF short_b bounds ground]
    by (simp add: lp_equations_def \<eta>'_def)
  have normalized: "lp_cut_normalize fuel
      [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))]
      (map (lp_cut_map (\<lambda>t. t\<cdot>lp_cut_refresh k (set G))) gs) = Some (Some next)"
    using checked by (simp add: lp_cut_check_unify_def)
  have evaluated: "map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>')) next =
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs"
    using lp_cut_normalize_success[OF normalized equations]
      lp_cut_resolution_active_goals[OF goals bounds ground, where \<sigma>=\<sigma> and \<rho>=\<eta>]
    by (simp add: \<eta>'_def)
  show "lp_cut_state_eval (LPCGoals next#es) \<eta>' =
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs)#lp_cut_state_eval es \<eta>"
    using evaluated lp_cut_resolution_saved_stack[OF saved kl, of \<eta> \<sigma> \<eta>]
    by (simp add: lp_cut_state_map_def \<eta>'_def)
  have old: "lp_cut_knowledge (set G) guards \<eta>'"
    unfolding \<eta>'_def
    by (rule lp_cut_resolution_knowledge_preserved[OF knowledge _ _ kl])
      (use checked in \<open>auto simp: lp_cut_check_unify_def\<close>)
  have positive: "lp_cut_guard_holds (LPCEqGuard a b True) \<eta>'"
    using unifier lp_cut_resolution_old[OF short_a kl, of \<eta> \<sigma> \<eta>]
      lp_cut_resolution_old[OF short_b kl, of \<eta> \<sigma> \<eta>]
    by (auto simp: \<eta>'_def)
  show "lp_cut_knowledge (set G) (guards@[LPCEqGuard a b True]) \<eta>'"
    using old positive by (simp add: lp_cut_knowledge_def)
qed

lemma lp_cut_source_unify_cases:
  fixes a :: "('f lp_cut_symbol,'w) lp_iterm"
  assumes "(LPCGoals (LPCUnify a b#gs)#es,t)\<in>lp_cut_source P"
  shows "(\<exists>\<sigma>::'w\<Rightarrow>('f lp_cut_symbol,'w) lp_iterm.
      lp_isubst a \<sigma> = lp_isubst b \<sigma> \<and>
      t=LPCGoals (map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) gs)#es) \<or>
    (t=es \<and> \<not>(\<exists>\<sigma>::'w\<Rightarrow>('f lp_cut_symbol,'w) lp_iterm.
      lp_isubst a \<sigma> = lp_isubst b \<sigma>))"
  using assms by (cases rule: lp_cut_source.cases) auto

theorem lp_cut_checked_unify_covers:
  fixes \<eta> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lp_cut_check_unify fuel k l G guards a b gs es next"
    and coverage: "lp_cut_check_equality fuel a b mode"
    and not_failure: "mode\<noteq>LPCAlwaysFailure"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
    and step: "(lp_cut_state_eval (LPCGoals (LPCUnify a b#gs)#es) \<eta>,t)\<in>lp_cut_source P"
  shows "(\<exists>\<eta>'. t=lp_cut_state_eval (LPCGoals next#es) \<eta>' \<and>
      lp_cut_knowledge (set G)
        (if mode=LPCBoth then guards@[LPCEqGuard a b True] else guards) \<eta>') \<or>
    (mode=LPCBoth \<and> t=lp_cut_state_eval es \<eta> \<and>
      lp_cut_knowledge (set G) (guards@[LPCEqGuard a b False]) \<eta>)"
proof -
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  have src: "(LPCGoals (LPCUnify (lp_ieval a \<eta>) (lp_ieval b \<eta>)#?gs)#?es,t)\<in>lp_cut_source P"
    using step by (simp add: lp_cut_state_map_def)
  from lp_cut_source_unify_cases[OF src] show ?thesis
  proof
    assume "\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma> \<and>
      t=LPCGoals (map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es"
    then obtain \<sigma> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
      where unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
      and successor: "t=LPCGoals (map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es" by blast
    let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<eta>"
    have eq: "t=lp_cut_state_eval (LPCGoals next#es) ?env"
      using lp_cut_checked_unify_success(1)[OF checked knowledge unifier] successor
      by (simp add: map_map o_def lp_cut_map_comp)
    have domain: "lp_cut_knowledge (set G)
      (if mode=LPCBoth then guards@[LPCEqGuard a b True] else guards) ?env"
      using lp_cut_checked_unify_success(2)[OF checked knowledge unifier]
      by (auto simp: lp_cut_knowledge_def)
    show ?thesis using eq domain by blast
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>)"
    have "mode\<noteq>LPCAlwaysSuccess"
      using coverage failure lp_cut_equality_success[of fuel a b \<eta>]
      by blast
    then have both: "mode=LPCBoth" using not_failure by (cases mode) auto
    have domain: "lp_cut_knowledge (set G) (guards@[LPCEqGuard a b False]) \<eta>"
      using knowledge failure by (simp add: lp_cut_knowledge_def)
    show ?thesis using both domain failure by blast
  qed
qed

end
