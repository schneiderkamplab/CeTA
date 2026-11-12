theory LP_Cut_NO_Renamed_Permutation
 imports LP_Cut_NO_Return_Permutation LP_Cut_NO_Swap_Support
begin

lemma lpc_permutation_rename_term:
 assumes inverse: "\<And>z. p (p z) = z"
 shows "(t\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))\<cdot>(Var \<circ> p) =
   (t\<cdot>(Var \<circ> p))\<cdot>(\<lambda>v. Var (lpc_no_permute (map (\<lambda>(x,y). (p x,p y)) swaps) v))"
 by (induct t) (auto simp: o_def lpc_no_permute_rename[OF inverse] intro!: map_cong)

lemma lpc_no_return_permutation_renamed_ambient:
 fixes P :: "('f,string) lp_cut_program"
 assumes checked: "lpc_no_return_resolve_permutation fuel P a gs c m original_saved payload k V images swaps successor_goals result"
   and inverse: "\<And>x. p (p x) = x"
   and head_vars: "vars_term (fst (P!c)) \<subseteq> B"
   and body_vars: "\<forall>g\<in>set (snd (P!c)). \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> B"
   and fresh_extra: "\<And>t. t\<in>set extra \<Longrightarrow>
     vars_term t \<inter> (p \<circ> lp_prefix k) ` B = {}"
   and fixed_extra: "map (\<lambda>t.
     (t\<cdot>lpc_conjugate_substitution p (lpc_mgu_substitution V images))\<cdot>
       (\<lambda>v. Var (lpc_no_permute (map (\<lambda>(x,y). (p x,p y)) swaps) v))) extra = extra"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCClause (LPCAtom (a\<cdot>(Var \<circ> p))#map (lp_cut_map (\<lambda>t. t\<cdot>(Var \<circ> p))) gs) c m,
       map (\<lambda>t. t\<cdot>(Var \<circ> p)) payload @ extra)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>(Var \<circ> p))) successor_goals),
       map (\<lambda>t. t\<cdot>(Var \<circ> p)) result @ extra)#saved)))"
proof -
 let ?s = "lpc_mgu_substitution V images"
 let ?r = "Var \<circ> p"
 let ?q = "p \<circ> lp_prefix k"
 let ?cs = "lpc_conjugate_substitution p ?s"
 have index: "c<length P"
   and short: "\<forall>x\<in>vars_term a. length x<k"
   and goals: "lp_cut_short_goals k (gs @ map LPCAtom payload)"
   and mgu: "lpc_check_mgu fuel [(a,fst (P!c)\<cdot>(Var \<circ> lp_prefix k))] V images"
   and successor: "successor_goals = map (lp_cut_bind m (\<lambda>t. (t\<cdot>(?s \<circ> lp_prefix k))\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. (t\<cdot>?s)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)))) gs"
   and result: "result = map (\<lambda>t. (t\<cdot>?s)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v))) payload"
   using checked by (auto simp: lpc_no_return_resolve_permutation_def lpc_no_resolve_permutation_def lp_cut_short_goals_def o_def)
 have global: "lpc_global_mgu [(a\<cdot>?r,fst (P!c)\<cdot>(Var \<circ> ?q))] ?cs"
   using lpc_global_mgu_conjugate[OF lpc_checked_global_mgu[OF mgu] inverse]
   by (simp only: lpc_rename_fresh_equation)
 have injective: "inj_on ?q B"
 proof (rule inj_onI)
   fix x y assume "x\<in>B" "y\<in>B" and equal: "?q x = ?q y"
   have "lp_prefix k x = lp_prefix k y"
     using arg_cong[OF equal, of p] by (simp add: o_def inverse)
   then show "x=y" by (simp add: lp_prefix_def)
 qed
 have fresh_a: "vars_term (a\<cdot>?r) \<inter> ?q ` B = {}"
   by (rule lpc_short_renamed_fresh[OF inverse short])
 have terms_map: "lp_cut_terms (lp_cut_map f g) = map f (lp_cut_terms g)" for f g
   by (cases g) auto
 have old_fresh: "\<forall>g\<in>set (gs @ map LPCAtom payload). \<forall>t\<in>set (lp_cut_terms g).
   vars_term (t\<cdot>?r) \<inter> ?q ` B = {}"
   by (intro ballI, rule lpc_short_renamed_fresh[OF inverse])
     (use goals in \<open>auto simp: lp_cut_short_goals_def list_all_iff\<close>)
 have fresh_goals: "\<forall>g\<in>set
   (map (lp_cut_map (\<lambda>t. t\<cdot>?r)) gs @
     map LPCAtom (map (\<lambda>t. t\<cdot>?r) payload @ extra)).
   \<forall>t\<in>set (lp_cut_terms g). vars_term t \<inter> ?q ` B = {}"
 proof (intro ballI)
   fix g t
   assume member: "g\<in>set (map (lp_cut_map (\<lambda>t. t\<cdot>?r)) gs @
     map LPCAtom (map (\<lambda>t. t\<cdot>?r) payload @ extra))"
     and term_member: "t\<in>set (lp_cut_terms g)"
   have alternatives: "g\<in>set (map (lp_cut_map (\<lambda>t. t\<cdot>?r)) (gs @ map LPCAtom payload)) \<or>
     g\<in>set (map LPCAtom extra)"
     using member by (auto simp: map_map o_def)
   show "vars_term t \<inter> ?q ` B = {}"
   proof (cases "g\<in>set (map (lp_cut_map (\<lambda>t. t\<cdot>?r)) (gs @ map LPCAtom payload))")
     case True
     then obtain h where h: "h\<in>set (gs @ map LPCAtom payload)" "g=lp_cut_map (\<lambda>t. t\<cdot>?r) h" by (auto simp only: set_map)
     obtain u where u: "u\<in>set (lp_cut_terms h)" "t=u\<cdot>?r"
       using term_member h(2) by (auto simp only: terms_map set_map)
     note fresh_u = bspec[OF bspec[OF old_fresh h(1)] u(1)]
     show ?thesis using fresh_u by (simp only: u(2))
   next
     case False
     have "g\<in>set (map LPCAtom extra)" using alternatives False by blast
     then obtain u where u: "u\<in>set extra" "g=LPCAtom u" by auto
     have "t=u" using term_member u(2) by simp
     then show ?thesis using fresh_extra[OF u(1)] by simp
   qed
 qed
 note step = lpc_global_return_resolve_permutation_ambient[OF index global injective head_vars body_vars fresh_a fresh_goals fixed_extra,
   of rest m saved]
 show ?thesis using step
   by (simp add: successor result map_map o_def lp_cut_map_comp lp_cut_map_bind
     lpc_permutation_rename_term[OF inverse, unfolded o_def]
     lpc_conjugate_substitution_apply[OF inverse, unfolded o_def] lpc_conjugate_clause_update[OF inverse, unfolded o_def])
qed

lemma lpc_permuted_substitution_support:
 assumes lengths: "length V=length images"
   and outside: "z\<notin>set V \<union> lpc_no_permutation_support swaps"
 shows "(lpc_mgu_substitution V images z)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v)) = Var z"
 using outside by (simp add: lpc_mgu_substitution_outside[OF lengths] lpc_no_permute_outside)

lemma lpc_conjugate_permuted_substitution:
 assumes inverse: "\<And>z. p (p z) = z"
 shows "lpc_conjugate_substitution p
   (\<lambda>z. (substitution z)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v))) z =
   (lpc_conjugate_substitution p substitution z)\<cdot>(\<lambda>v. Var (lpc_no_permute (map (\<lambda>(x,y). (p x,p y)) swaps) v))"
 by (simp add: lpc_conjugate_substitution_def lpc_permutation_rename_term[OF inverse])

lemma lpc_renamed_permutation_fixes_ambient:
 assumes inverse: "\<And>z. p (p z) = z"
   and lengths: "length V=length images"
   and outside: "\<And>z. z\<in>\<Union>(vars_term ` set extra) \<Longrightarrow>
     z\<notin>p ` (set V \<union> lpc_no_permutation_support swaps)"
 shows "map (\<lambda>t. (t\<cdot>lpc_conjugate_substitution p (lpc_mgu_substitution V images))\<cdot>
   (\<lambda>v. Var (lpc_no_permute (map (\<lambda>(x,y). (p x,p y)) swaps) v))) extra = extra"
proof -
 let ?sub = "\<lambda>z. (lpc_mgu_substitution V images z)\<cdot>(\<lambda>v. Var (lpc_no_permute swaps v))"
 have fixed: "map (\<lambda>t. t\<cdot>lpc_conjugate_substitution p ?sub) extra = extra"
   by (rule lpc_substitution_fixes_ambient_terms,
     rule lpc_conjugate_supported_outside[where S="set V \<union> lpc_no_permutation_support swaps" and substitution="?sub", OF inverse],
     rule lpc_permuted_substitution_support[OF lengths], assumption, rule outside)
 have applied: "t\<cdot>lpc_conjugate_substitution p ?sub =
   (t\<cdot>lpc_conjugate_substitution p (lpc_mgu_substitution V images))\<cdot>
     (\<lambda>v. Var (lpc_no_permute (map (\<lambda>(x,y). (p x,p y)) swaps) v))" for t
   by (induct t) (auto simp: lpc_conjugate_permuted_substitution[OF inverse] intro!: map_cong)
 show ?thesis using fixed by (simp only: applied)
qed

ML \<open>
val checked = [@{thm lpc_no_return_permutation_renamed_ambient},
 @{thm lpc_renamed_permutation_fixes_ambient}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted renamed output permutation" else ();
\<close>
end
