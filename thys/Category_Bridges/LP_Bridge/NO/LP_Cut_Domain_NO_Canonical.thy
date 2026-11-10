theory LP_Cut_Domain_NO_Canonical
  imports LP_Cut_Back_Representation
begin

lemma logic_flat_goal_map:
  "concat (map logic_goal_terms (map (logic_goal_map f) gs)) =
   map f (concat (map logic_goal_terms gs))"
proof -
  have single: "logic_goal_terms (logic_goal_map f g) = map f (logic_goal_terms g)" for g
    by (cases g) auto
  show ?thesis by (induct gs) (simp_all add: single)
qed
lemma logic_flat_equal:
  assumes "map (logic_goal_map f) gs = map (logic_goal_map g) gs"
  shows "map (logic_atom_map f) (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms gs))) =
    map (logic_atom_map g) (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms gs)))"
proof -
  have "map f (concat (map logic_goal_terms gs)) = map g (concat (map logic_goal_terms gs))"
    using arg_cong[OF assms, of "\<lambda>xs. concat (map logic_goal_terms xs)"]
    by (simp only: logic_flat_goal_map)
  then show ?thesis
    using arg_cong[of _ _ "map (\<lambda>t. ((),[t]))"]
    by (simp add: logic_atom_map_def map_map o_def)
qed
lemma cut_back_maps_equal:
  assumes eq: "map (lp_cut_map f) gs = map (lp_cut_map g) gs"
    and f: "\<And>t. cut_tree_back (f t) = h (k t)"
    and g: "\<And>t. cut_tree_back (g t) = j (k t)"
  shows "map (logic_goal_map h) (map (cut_goal_back k) gs) =
    map (logic_goal_map j) (map (cut_goal_back k) gs)"
proof -
  have left: "cut_goal_back cut_tree_back (lp_cut_map f v) = logic_goal_map h (cut_goal_back k v)" for v
    by (rule cut_back_goal_map; rule f)
  have right: "cut_goal_back cut_tree_back (lp_cut_map g v) = logic_goal_map j (cut_goal_back k v)" for v
    by (rule cut_back_goal_map; rule g)
  show ?thesis using arg_cong[OF eq, of "map (cut_goal_back cut_tree_back)"]
    by (simp only: map_map o_def left right)
qed

context cut_runtime_domain
begin

lemma canonical_mgu_resolve:
  assumes mgu: "mgu_resolve a gs h bs sigma rho"
  shows "logic_cut_mgu (\<lambda>t. D (cut_tree t)) (cut_tree_back a)
    (map (cut_goal_back cut_tree_back) gs) (cut_term_back h)
    (map (cut_goal_back cut_term_back) bs)
    (cut_tree_back \<circ> sigma) (cut_tree_back \<circ> rho)"
proof -
  have ds: "\<forall>x. D (sigma x)" and dr: "\<forall>x. D (rho x)"
    and eq: "lp_isubst a sigma = lp_ieval h rho"
    using mgu by (auto simp: mgu_resolve_def)
  show ?thesis unfolding logic_cut_mgu_def logic_mgu_def
  proof (intro conjI)
    show "logic_substitution (\<lambda>t. D (cut_tree t)) (cut_tree_back \<circ> sigma)"
      using ds by (simp add: logic_substitution_def)
    show "logic_substitution (\<lambda>t. D (cut_tree t)) (cut_tree_back \<circ> rho)"
      using dr by (simp add: logic_substitution_def)
    show "logic_atom_map (logic_subst (cut_tree_back \<circ> sigma)) ((),[cut_tree_back a]) =
      logic_atom_map (logic_eval (cut_tree_back \<circ> rho)) ((),[cut_term_back h])"
      using arg_cong[OF eq, of cut_tree_back]
      by (simp add: logic_atom_map_def cut_back_subst cut_back_eval)
    show "\<forall>t u. logic_substitution (\<lambda>t. D (cut_tree t)) t \<longrightarrow>
      logic_substitution (\<lambda>t. D (cut_tree t)) u \<longrightarrow>
      logic_atom_map (logic_subst t) ((),[cut_tree_back a]) =
        logic_atom_map (logic_eval u) ((),[cut_term_back h]) \<longrightarrow>
      (\<exists>d. logic_substitution (\<lambda>t. D (cut_tree t)) d \<and>
        logic_atom_map (logic_subst d \<circ> logic_subst (cut_tree_back \<circ> sigma)) ((),[cut_tree_back a]) =
          logic_atom_map (logic_subst t) ((),[cut_tree_back a]) \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_subst (cut_tree_back \<circ> sigma)))
          (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms (map (cut_goal_back cut_tree_back) gs)))) =
        map (logic_atom_map (logic_subst t))
          (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms (map (cut_goal_back cut_tree_back) gs)))) \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_eval (cut_tree_back \<circ> rho)))
          (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms (map (cut_goal_back cut_term_back) bs)))) =
        map (logic_atom_map (logic_eval u))
          (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms (map (cut_goal_back cut_term_back) bs)))))"
    proof (intro allI impI)
      fix t u
      assume dt: "logic_substitution (\<lambda>t. D (cut_tree t)) t"
        and du: "logic_substitution (\<lambda>t. D (cut_tree t)) u"
        and eq: "logic_atom_map (logic_subst t) ((),[cut_tree_back a]) =
          logic_atom_map (logic_eval u) ((),[cut_term_back h])"
      have eq': "lp_isubst a (cut_tree \<circ> t) = lp_ieval h (cut_tree \<circ> u)"
        using eq cut_back_subst[of a "cut_tree \<circ> t"] cut_back_eval[of h "cut_tree \<circ> u"]
        by (simp add: logic_atom_map_def o_def; metis cut_tree_native_roundtrip)
      obtain delta where dd: "\<forall>x. D (delta x)" and atom:
        "lp_isubst (lp_isubst a sigma) delta = lp_isubst a (cut_tree \<circ> t)"
        and goals: "map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v sigma) delta)) gs =
          map (lp_cut_map (\<lambda>v. lp_isubst v (cut_tree \<circ> t))) gs"
        and body: "map (lp_cut_map (\<lambda>v. lp_isubst (lp_ieval v rho) delta)) bs =
          map (lp_cut_map (\<lambda>v. lp_ieval v (cut_tree \<circ> u))) bs"
        using spec[OF spec[OF conjunct2[OF conjunct2[OF conjunct2[OF mgu[unfolded mgu_resolve_def]]]], of "cut_tree \<circ> t"], of "cut_tree \<circ> u"] dt du eq'
        by (simp only: logic_substitution_def o_apply) blast
      let ?d = "cut_tree_back \<circ> delta"
      have goals': "map (logic_goal_map (logic_subst ?d \<circ> logic_subst (cut_tree_back \<circ> sigma)))
        (map (cut_goal_back cut_tree_back) gs) =
        map (logic_goal_map (logic_subst t)) (map (cut_goal_back cut_tree_back) gs)"
        by (rule cut_back_maps_equal[OF goals]) (simp_all add: cut_back_subst o_def)
      have body': "map (logic_goal_map (logic_subst ?d \<circ> logic_eval (cut_tree_back \<circ> rho)))
        (map (cut_goal_back cut_term_back) bs) =
        map (logic_goal_map (logic_eval u)) (map (cut_goal_back cut_term_back) bs)"
        by (rule cut_back_maps_equal[OF body]) (simp_all add: cut_back_subst cut_back_eval o_def)
      show "\<exists>d. logic_substitution (\<lambda>t. D (cut_tree t)) d \<and>
        logic_atom_map (logic_subst d \<circ> logic_subst (cut_tree_back \<circ> sigma)) ((),[cut_tree_back a]) =
          logic_atom_map (logic_subst t) ((),[cut_tree_back a]) \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_subst (cut_tree_back \<circ> sigma)))
          (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms (map (cut_goal_back cut_tree_back) gs)))) =
        map (logic_atom_map (logic_subst t))
          (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms (map (cut_goal_back cut_tree_back) gs)))) \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_eval (cut_tree_back \<circ> rho)))
          (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms (map (cut_goal_back cut_term_back) bs)))) =
        map (logic_atom_map (logic_eval u))
          (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms (map (cut_goal_back cut_term_back) bs))))"
        apply (rule exI[of _ ?d], intro conjI)
           apply (simp add: logic_substitution_def dd)
          apply (use arg_cong[OF atom, of cut_tree_back] in
            \<open>simp add: logic_atom_map_def cut_back_subst o_def\<close>)
         apply (rule logic_flat_equal[OF goals'])
        apply (rule logic_flat_equal[OF body'])
        done
    qed
  qed
qed

lemma canonical_mgu_unify:
  assumes mgu: "mgu_unify a b gs sigma"
  shows "logic_unify_mgu (\<lambda>t. D (cut_tree t)) (cut_tree_back a) (cut_tree_back b)
    (map (cut_goal_back cut_tree_back) gs) (cut_tree_back \<circ> sigma)"
proof -
  have ds: "\<forall>x. D (sigma x)" and eq: "lp_isubst a sigma = lp_isubst b sigma"
    using mgu by (auto simp: mgu_unify_def)
  have factor: "\<exists>d. logic_substitution (\<lambda>t. D (cut_tree t)) d \<and>
    logic_subst d (logic_subst (cut_tree_back \<circ> sigma) (cut_tree_back a)) = logic_subst t (cut_tree_back a) \<and>
    map (logic_goal_map (logic_subst d \<circ> logic_subst (cut_tree_back \<circ> sigma)))
      (map (cut_goal_back cut_tree_back) gs) =
    map (logic_goal_map (logic_subst t)) (map (cut_goal_back cut_tree_back) gs)"
    if dt: "logic_substitution (\<lambda>t. D (cut_tree t)) t"
      and eq: "logic_subst t (cut_tree_back a) = logic_subst t (cut_tree_back b)" for t
  proof -
    have eq': "lp_isubst a (cut_tree \<circ> t) = lp_isubst b (cut_tree \<circ> t)"
      using arg_cong[OF eq, of cut_tree] by (simp add: cut_tree_subst)
    obtain delta where dd: "\<forall>x. D (delta x)" and atom:
      "lp_isubst (lp_isubst a sigma) delta = lp_isubst a (cut_tree \<circ> t)"
      and goals: "map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v sigma) delta)) gs =
        map (lp_cut_map (\<lambda>v. lp_isubst v (cut_tree \<circ> t))) gs"
      using spec[OF conjunct2[OF conjunct2[OF mgu[unfolded mgu_unify_def]]], of "cut_tree \<circ> t"] dt eq'
      by (simp only: logic_substitution_def o_apply) blast
    have goals': "map (logic_goal_map (logic_subst (cut_tree_back \<circ> delta) \<circ> logic_subst (cut_tree_back \<circ> sigma)))
      (map (cut_goal_back cut_tree_back) gs) =
      map (logic_goal_map (logic_subst t)) (map (cut_goal_back cut_tree_back) gs)"
      by (rule cut_back_maps_equal[OF goals]) (simp_all add: cut_back_subst o_def)
    show ?thesis by (rule exI[of _ "cut_tree_back \<circ> delta"])
      (use dd arg_cong[OF atom, of cut_tree_back] goals' in
        \<open>simp add: logic_substitution_def cut_back_subst o_def\<close>)
  qed
  show ?thesis unfolding logic_unify_mgu_def
    using ds arg_cong[OF eq, of cut_tree_back] factor
    by (auto simp: logic_substitution_def cut_back_subst)
qed

lemma canonical_no_step:
  assumes "(s,t)\<in>mgu_source P"
  shows "logic_cut_step (\<lambda>t. D (cut_tree t)) (cut_program_back P) (cut_state_back s) (cut_state_back t)"
  using assms
proof (cases rule: mgu_source.cases)
  case admin
  then show ?thesis by (auto intro: logic_cut_step.admin cut_back_admin)
next
  case (case_call m f ts gs es)
  have fresh: "logic_fresh_mark m (cut_state_back (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es))"
    by (rule cut_back_fresh) (use case_call in blast)
  show ?thesis using logic_cut_step.case_call[OF fresh[simplified], where P="cut_program_back P" and D="\<lambda>t. D (cut_tree t)"] case_call
    by (simp add: cut_back_slice map_map o_def)
next
  case (resolve c a gs sigma rho m es)
  have mgu: "logic_cut_mgu (\<lambda>t. D (cut_tree t)) (cut_tree_back a)
    (map (cut_goal_back cut_tree_back) gs) (fst (cut_program_back P!c)) (snd (cut_program_back P!c))
    (cut_tree_back \<circ> sigma) (cut_tree_back \<circ> rho)"
    using canonical_mgu_resolve[OF resolve(4)] resolve(3) by (simp add: cut_back_program_nth)
  have index: "c<length (cut_program_back P)" using resolve by simp
  show ?thesis using logic_cut_step.resolve[OF index mgu, of m "cut_state_back es"] resolve
    by (simp add: cut_back_program_nth map_map o_def
      cut_back_goal_subst cut_back_goal_eval_bind)
next
  case (backtrack c a gs m)
  have index: "c<length (cut_program_back P)" using backtrack by simp
  have failure: "\<not>(\<exists>sigma rho. logic_substitution (\<lambda>t. D (cut_tree t)) sigma \<and>
    logic_substitution (\<lambda>t. D (cut_tree t)) rho \<and>
    logic_subst sigma (cut_tree_back a) = logic_eval rho (fst (cut_program_back P!c)))"
  proof
    assume "\<exists>sigma rho. logic_substitution (\<lambda>t. D (cut_tree t)) sigma \<and>
      logic_substitution (\<lambda>t. D (cut_tree t)) rho \<and>
      logic_subst sigma (cut_tree_back a) = logic_eval rho (fst (cut_program_back P!c))"
    then obtain sigma rho where eq: "logic_subst sigma (cut_tree_back a) = logic_eval rho (cut_term_back (fst (P!c)))"
      using backtrack(2) by (auto simp: cut_back_program_nth)
    have "lp_isubst a (cut_tree \<circ> sigma) = lp_ieval (fst (P!c)) (cut_tree \<circ> rho)"
      using eq cut_back_subst[of a "cut_tree \<circ> sigma"] cut_back_eval[of "fst(P!c)" "cut_tree \<circ> rho"]
      by (simp add: o_def; metis cut_tree_native_roundtrip)
    then show False using backtrack by blast
  qed
  show ?thesis using logic_cut_step.backtrack[OF index failure, of "map (cut_goal_back cut_tree_back) gs" m "cut_state_back t"] backtrack by simp
next
  case (unify a b gs sigma es)
  show ?thesis using logic_cut_step.unify[OF canonical_mgu_unify[OF unify(3)], where es="cut_state_back es" and P="cut_program_back P"] unify
    by (simp add: map_map o_def cut_back_goal_subst)
next
  case (unify_fail a b gs)
  have failure: "\<not>(\<exists>sigma. logic_substitution (\<lambda>t. D (cut_tree t)) sigma \<and>
    logic_subst sigma (cut_tree_back a) = logic_subst sigma (cut_tree_back b))"
    using unify_fail(2) cut_tree_subst[of _ "cut_tree_back a"] cut_tree_subst[of _ "cut_tree_back b"]
    by (metis cut_tree_native_roundtrip)
  show ?thesis using logic_cut_step.unify_fail[OF failure, where gs="map (cut_goal_back cut_tree_back) gs" and es="cut_state_back t" and P="cut_program_back P"] unify_fail by simp
next
  case (meta m a gs es body)
  obtain f ts where a: "a=LPIFun f ts" using meta by blast
  have fresh: "logic_fresh_mark m (cut_state_back (LPCGoals (LPCMeta a#gs)#es))"
    by (rule cut_back_fresh) (use meta in blast)
  have lower: "logic_lower m (cut_tree_back a) (map (cut_goal_back cut_tree_back) body)"
    by (rule cut_back_lower) (use meta in blast)
  show ?thesis using logic_cut_step.meta[OF fresh[unfolded a, simplified] lower[unfolded a, simplified], where P="cut_program_back P" and D="\<lambda>t. D (cut_tree t)"] meta a
    by simp
qed

end
end
