theory LP_Cut_NO_Return_Permutation
 imports LP_Cut_NO_Permutation
begin

definition lpc_no_resolve_permutation where
  "lpc_no_resolve_permutation fuel P a gs c m es k V images swaps successor =
    (c<length P \<and> (\<forall>v\<in>vars_term a. length v<k) \<and>
     lp_cut_short_goals k gs \<and>
     lpc_check_mgu fuel [(a,fst (P!c)\<cdot>(\<lambda>v. Var (lp_prefix k v)))] V images \<and>
     successor=LPCGoals
       (map (lp_cut_bind m (\<lambda>t. (t\<cdot>(\<lambda>v. lpc_mgu_substitution V images (lp_prefix k v)))\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. (t\<cdot>lpc_mgu_substitution V images)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))) gs)#es)"

theorem lpc_no_resolve_permutation_sound:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_no_resolve_permutation fuel P a gs c m es k V images swaps successor"
  shows "(lp_cut_state_eval (LPCClause (LPCAtom a#gs) c m#es) LPIVar,
          lp_cut_state_eval successor LPIVar)\<in>lp_cut_mgu_source P"
proof -
  have index: "c<length P"
    and short: "\<forall>v\<in>vars_term a. length v<k" "lp_cut_short_goals k gs"
    and mgu: "lpc_check_mgu fuel [(a,fst (P!c)\<cdot>(\<lambda>v. Var (lp_prefix k v)))] V images"
    using checked by (auto simp: lpc_no_resolve_permutation_def)
  have actual: "lpc_mgu_resolve (lp_ieval a LPIVar)
      (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) (fst (P!c)) (snd (P!c))
      (\<lambda>v. lp_ieval (lpc_mgu_substitution V images v) LPIVar)
      (\<lambda>v. lp_ieval (lpc_mgu_substitution V images (lp_prefix k v)) LPIVar)"
    by (rule lpc_checked_mgu_resolve[OF mgu short])
  show ?thesis
    using lp_cut_mgu_source.resolve[OF index lpc_mgu_resolve_output_permutation[OF actual, of swaps],
      of m "lp_cut_state_eval es LPIVar"] checked
    by (simp add: lpc_no_resolve_permutation_def lp_cut_state_map_def map_map o_def
      lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

definition lpc_no_return_resolve_permutation where
 "lpc_no_return_resolve_permutation fuel P a gs c m saved payload k V images swaps successor_goals result =
   (lpc_no_resolve_permutation fuel P a gs c m (map fst saved) k V images swaps
      (LPCGoals successor_goals#map fst saved) \<and>
    lp_cut_short_goals k (map LPCAtom payload) \<and>
    result = map (\<lambda>t. (t\<cdot>lpc_mgu_substitution V images)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v))) payload)"

lemma lpc_no_return_resolve_permutation_attach_sound:
 fixes P :: "('f,string) lp_cut_program"
 assumes checked: "lpc_no_return_resolve_permutation fuel P a gs c m saved payload k V images swaps successor_goals result"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest
     (lpc_return_eval LPIVar ((LPCClause (LPCAtom a#gs) c m,payload)#saved))) None
   (lpc_attach_answers rest
     (lpc_return_eval LPIVar ((LPCGoals successor_goals,result)#saved)))"
proof -
 let ?s = "lpc_mgu_substitution V images"
 have index: "c<length P"
   and short: "\<forall>x\<in>vars_term a. length x<k"
   and goals: "lp_cut_short_goals k (gs @ map LPCAtom payload)"
   and mgu: "lpc_check_mgu fuel [(a,fst (P!c)\<cdot>(\<lambda>x. Var (lp_prefix k x)))] V images"
   and successor_goals: "successor_goals = map (lp_cut_bind m (\<lambda>t. (t\<cdot>(\<lambda>v. ?s (lp_prefix k v)))\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. (t\<cdot>?s)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))) gs"
   and result: "result = map (\<lambda>t. (t\<cdot>?s)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v))) payload"
   using checked by (auto simp: lpc_no_return_resolve_permutation_def lpc_no_resolve_permutation_def lp_cut_short_goals_def)
 have actual: "lpc_mgu_resolve (lp_ieval a LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs @
     map (\<lambda>t. LPCAtom (lp_ieval t LPIVar)) payload)
   (fst (P!c)) (snd (P!c))
   (\<lambda>x. lp_ieval (?s x) LPIVar)
   (\<lambda>x. lp_ieval (?s (lp_prefix k x)) LPIVar)"
   using lpc_checked_mgu_resolve[OF mgu short goals]
   by (simp add: map_map o_def)
 have answers: "lpc_return_env result LPIVar =
   (\<lambda>n. lp_isubst (lpc_return_env payload LPIVar n) (\<lambda>v. lp_isubst (lp_ieval (?s v) LPIVar) (\<lambda>w. LPIVar (lpc_no_permute swaps w))))"
   by (rule lpc_return_env_active)
     (simp add: result map_map o_def lp_ieval_finite_subst lp_ieval_subst)
 note swapped = lpc_mgu_resolve_output_permutation[OF actual, of swaps]
 note step = lpc_return_resolve_attach[OF index swapped,
   of rest m "lpc_return_eval LPIVar saved"]
 show ?thesis using step
   by (simp add: lpc_return_eval_def successor_goals answers map_map o_def
     lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

lemma lpc_global_return_resolve_permutation_ambient:
 fixes P :: "('f,string) lp_cut_program"
 assumes index: "c<length P"
   and mgu: "lpc_global_mgu [(a,fst (P!c)\<cdot>(Var \<circ> rename_clause_var))] substitution"
   and injective: "inj_on rename_clause_var B"
   and head_vars: "vars_term (fst (P!c)) \<subseteq> B"
   and body_vars: "\<forall>g\<in>set (snd (P!c)). \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> B"
   and fresh_a: "vars_term a \<inter> rename_clause_var ` B = {}"
   and fresh_goals: "\<forall>g\<in>set (gs @ map LPCAtom (payload@extra)). \<forall>t\<in>set (lp_cut_terms g).
     vars_term t \<inter> rename_clause_var ` B = {}"
   and fixed: "map (\<lambda>t. (t\<cdot>substitution)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v))) extra = extra"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCClause (LPCAtom a#gs) c m,payload@extra)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_bind m (\<lambda>t. (t\<cdot>(substitution \<circ> rename_clause_var))\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. (t\<cdot>substitution)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))) gs),
       map (\<lambda>t. (t\<cdot>substitution)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v))) payload @ extra)#saved)))"
proof -
 have actual: "lpc_mgu_resolve (lp_ieval a LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs @
     map (\<lambda>t. LPCAtom (lp_ieval t LPIVar)) (payload@extra))
   (fst (P!c)) (snd (P!c))
   (\<lambda>x. lp_ieval (substitution x) LPIVar)
   (\<lambda>x. lp_ieval (substitution (rename_clause_var x)) LPIVar)"
   using lpc_global_mgu_resolve_fresh_support[OF mgu[unfolded o_def] injective head_vars body_vars fresh_a fresh_goals]
   by (simp add: map_map o_def)
 have answers: "lpc_return_env
   (map (\<lambda>t. (t\<cdot>substitution)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v))) payload @ extra) LPIVar =
   (\<lambda>n. lp_isubst (lpc_return_env (payload@extra) LPIVar n)
     (\<lambda>v. lp_isubst (lp_ieval (substitution v) LPIVar) (\<lambda>w. LPIVar (lpc_no_permute swaps w))))"
   apply (rule lpc_return_env_active)
   using arg_cong[OF fixed, of "map (\<lambda>t. lp_ieval t LPIVar)"]
   by (simp add: map_map o_def lp_ieval_finite_subst lp_ieval_subst)
 note swapped = lpc_mgu_resolve_output_permutation[OF actual, of swaps]
 note step = lpc_return_resolve_attach[OF index swapped,
   of rest m "lpc_return_eval LPIVar saved"]
 show ?thesis using step
   by (simp add: lpc_return_eval_def answers map_map o_def
     lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

ML \<open>
val checked = [@{thm lpc_no_resolve_permutation_sound},
 @{thm lpc_no_return_resolve_permutation_attach_sound},
 @{thm lpc_global_return_resolve_permutation_ambient}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return permutation dependency" else ();
\<close>
end
