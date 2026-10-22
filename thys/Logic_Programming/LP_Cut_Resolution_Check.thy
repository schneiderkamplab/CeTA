theory LP_Cut_Resolution_Check
  imports LP_Cut_Knowledge LP_Cut_Failure
begin

definition lp_cut_resolution_equations where
  "lp_cut_resolution_equations k l G a h =
    [(a\<cdot>lp_cut_refresh k (set G),h\<cdot>(\<lambda>x. Var (lp_prefix l x)))]"

definition lp_cut_check_resolution where
  "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors =
    (c<length P \<and> 2 * k \<le> l \<and>
     (\<forall>x\<in>vars_term a. length x<k) \<and> lp_cut_short_goals k gs \<and>
     (\<forall>e\<in>set es. lp_cut_short_entry k e) \<and>
     (\<forall>x\<in>set G. length x<k) \<and> set A \<subseteq> set G \<and>
     (\<forall>g\<in>set guards. lp_cut_short_guard k g) \<and>
     lp_cut_normalize fuel (lp_cut_resolution_equations k l G a (fst (P!c)))
       (map (lp_cut_bind m (\<lambda>t. t\<cdot>(\<lambda>x. Var (lp_prefix l x)))) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. t\<cdot>lp_cut_refresh k (set G))) gs) = Some (Some next) \<and>
     lp_cut_normalize fuel (lp_cut_resolution_equations k l G a (fst (P!c)))
       (map (\<lambda>x. LPCAtom (Var x)) A) = Some (Some (map LPCAtom anchors)))"

definition lp_cut_anchor_vars where
  "lp_cut_anchor_vars anchors = \<Union>(vars_term ` set anchors)"

text \<open>The concrete successor comes from any source unifier, not a trusted
substitution in the receipt. Both the control payload and the claimed new ground
information are independently recomputed by executable normalization.\<close>

theorem lp_cut_check_resolution_success:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
    and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
  defines "\<eta>' \<equiv> lp_cut_resolution_env k l \<eta> \<sigma> \<rho>"
  shows "lp_cut_state_eval (LPCGoals next#es) \<eta>' =
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs) # lp_cut_state_eval es \<eta>"
    and "lp_cut_knowledge (set G \<union> lp_cut_anchor_vars anchors)
      (guards@[LPCHeadGuard a (fst (P!c)) True]) \<eta>'"
proof -
  have short: "\<forall>x\<in>vars_term a. length x<k"
    and goals: "lp_cut_short_goals k gs"
    and saved: "\<forall>e\<in>set es. lp_cut_short_entry k e"
    and bounds: "2 * k \<le> l"
    using checked by (auto simp: lp_cut_check_resolution_def)
  have kl: "k\<le>l" using bounds by arith
  have ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
    using knowledge by (simp add: lp_cut_knowledge_def)
  have normalized: "lp_cut_normalize fuel
      [(a\<cdot>lp_cut_refresh k (set G),(fst (P!c))\<cdot>(\<lambda>x. Var (lp_prefix l x)))]
      (map (lp_cut_bind m (\<lambda>t. t\<cdot>(\<lambda>x. Var (lp_prefix l x)))) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. t\<cdot>lp_cut_refresh k (set G))) gs) = Some (Some next)"
    using checked by (simp add: lp_cut_check_resolution_def lp_cut_resolution_equations_def)
  show "lp_cut_state_eval (LPCGoals next#es) \<eta>' =
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs) # lp_cut_state_eval es \<eta>"
    unfolding \<eta>'_def
    by (rule lp_cut_normalized_resolution_covers_success[OF short goals saved bounds ground unifier normalized])
  have old: "lp_cut_knowledge (set G) guards \<eta>'"
    unfolding \<eta>'_def
    by (rule lp_cut_resolution_knowledge_preserved[OF knowledge _ _ kl])
      (use checked in \<open>auto simp: lp_cut_check_resolution_def\<close>)
  have equations: "lp_equations (lp_cut_resolution_equations k l G a (fst (P!c))) \<eta>'"
    using unifier lp_cut_resolution_active[OF short bounds ground]
    by (simp add: lp_cut_resolution_equations_def lp_equations_def \<eta>'_def lp_cut_resolution_clause)
  have anchor_ground: "\<forall>x\<in>set A. lp_seg_ground (\<eta>' x)"
    using old checked by (auto simp: lp_cut_knowledge_def lp_cut_check_resolution_def)
  have anchors_checked: "lp_cut_normalize fuel (lp_cut_resolution_equations k l G a (fst (P!c)))
      (map (\<lambda>x. LPCAtom (Var x)) A) = Some (Some (map LPCAtom anchors))"
    using checked by (simp add: lp_cut_check_resolution_def)
  have new: "\<forall>x\<in>lp_cut_anchor_vars anchors. lp_seg_ground (\<eta>' x)"
    using lp_cut_normalized_anchors_ground[OF equations anchor_ground anchors_checked]
    by (auto simp: lp_cut_anchor_vars_def)
  have positive: "lp_cut_guard_holds (LPCHeadGuard a (fst (P!c)) True) \<eta>'"
    unfolding \<eta>'_def by (rule lp_cut_resolution_positive_guard[OF short kl unifier])
  show "lp_cut_knowledge (set G \<union> lp_cut_anchor_vars anchors)
      (guards@[LPCHeadGuard a (fst (P!c)) True]) \<eta>'"
    using old new positive by (auto simp: lp_cut_knowledge_def)
qed

lemma lp_cut_source_clause_cases:
  fixes a :: "('f lp_cut_symbol,'w) lp_iterm"
  assumes "(LPCClause (LPCAtom a#gs) c m#es,t)\<in>lp_cut_source P"
  shows "(\<exists>\<sigma>::'w\<Rightarrow>('f lp_cut_symbol,'w) lp_iterm. \<exists>\<rho>.
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho> \<and>
      t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) gs)#es) \<or>
    (t=es \<and> \<not>(\<exists>\<sigma>::'w\<Rightarrow>('f lp_cut_symbol,'w) lp_iterm. \<exists>\<rho>.
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>))"
  using assms by (cases rule: lp_cut_source.cases) auto

theorem lp_cut_check_resolution_covers:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors"
    and coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) bindings mode"
    and not_failure: "mode\<noteq>LPCAlwaysFailure"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
    and step: "(lp_cut_state_eval (LPCClause (LPCAtom a#gs) c m#es) \<eta>,t)\<in>lp_cut_source P"
  shows "(\<exists>\<eta>'. t=lp_cut_state_eval (LPCGoals next#es) \<eta>' \<and>
      lp_cut_knowledge (set G \<union> lp_cut_anchor_vars anchors)
        (if mode=LPCBoth then guards@[LPCHeadGuard a (fst (P!c)) True] else guards) \<eta>') \<or>
    (mode=LPCBoth \<and> t=lp_cut_state_eval es \<eta> \<and>
      lp_cut_knowledge (set G) (guards@[LPCHeadGuard a (fst (P!c)) False]) \<eta>)"
proof -
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  have src: "(LPCClause (LPCAtom (lp_ieval a \<eta>)#?gs) c m#?es,t)\<in>lp_cut_source P"
    using step by (simp add: lp_cut_state_map_def)
  from lp_cut_source_clause_cases[OF src] show ?thesis
  proof
    assume "\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho> \<and>
      t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es"
    then obtain \<sigma> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
      and \<rho> where unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
      and successor: "t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es" by blast
    let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<rho>"
    have eq: "t=lp_cut_state_eval (LPCGoals next#es) ?env"
      using lp_cut_check_resolution_success(1)[OF checked knowledge unifier] successor
      by (simp add: map_map o_def lp_cut_map_comp)
    have domain: "lp_cut_knowledge (set G \<union> lp_cut_anchor_vars anchors)
      (if mode=LPCBoth then guards@[LPCHeadGuard a (fst (P!c)) True] else guards) ?env"
      using lp_cut_check_resolution_success(2)[OF checked knowledge unifier]
      by (auto simp: lp_cut_knowledge_def)
    show ?thesis using eq domain by blast
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>)"
    have "mode\<noteq>LPCAlwaysSuccess"
      using lp_cut_coverage_success[OF coverage, of \<eta>] failure by blast
    then have both: "mode=LPCBoth" using not_failure by (cases mode) auto
    have domain: "lp_cut_knowledge (set G) (guards@[LPCHeadGuard a (fst (P!c)) False]) \<eta>"
      using knowledge failure by (simp add: lp_cut_knowledge_def)
    show ?thesis using both domain failure by blast
  qed
qed

end
