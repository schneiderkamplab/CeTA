theory LP_Cut_NO_Renamed_Return
 imports LP_Cut_NO_Ambient_Interface
begin

lemma lpc_rename_fresh_equation:
 "lpc_rename_equations p [(a,h\<cdot>(Var \<circ> q))] =
   [(a\<cdot>(Var \<circ> p),h\<cdot>(Var \<circ> (p \<circ> q)))]"
proof -
 have compose: "(t\<cdot>(Var \<circ> q))\<cdot>(Var \<circ> p) = t\<cdot>(Var \<circ> (p \<circ> q))" for t
   by (induct t) (auto simp: o_def intro!: map_cong)
 show ?thesis by (simp add: lpc_rename_equations_def compose)
qed

lemma lpc_conjugate_clause_update:
 assumes inverse: "\<And>x. p (p x) = x"
 shows "t\<cdot>(lpc_conjugate_substitution p s \<circ> (p \<circ> q)) =
   (t\<cdot>(s \<circ> q))\<cdot>(Var \<circ> p)"
 by (induct t) (auto simp: lpc_conjugate_substitution_def inverse o_def intro!: map_cong)

lemma lpc_short_renamed_fresh:
 assumes inverse: "\<And>x. p (p x) = x"
   and short: "\<forall>x\<in>vars_term t. length x < k"
 shows "vars_term (t\<cdot>(Var \<circ> p)) \<inter> (p \<circ> lp_prefix k) ` B = {}"
proof -
 have injective: "inj p" by (rule injI) (metis inverse)
 have original: "vars_term t \<inter> lp_prefix k ` B = {}"
   using short by (auto simp: lp_prefix_def)
 show ?thesis using original injective
   by (auto simp: vars_term_subst o_def inj_on_def)
qed

lemma lpc_no_return_resolve_renamed_ambient:
 fixes P :: "('f,string) lp_cut_program"
 assumes checked: "lpc_no_return_resolve fuel P a gs c m original_saved payload k V images successor_goals result"
   and inverse: "\<And>x. p (p x) = x"
   and head_vars: "vars_term (fst (P!c)) \<subseteq> B"
   and body_vars: "\<forall>g\<in>set (snd (P!c)). \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> B"
   and fresh_extra: "\<And>t. t\<in>set extra \<Longrightarrow>
     vars_term t \<inter> (p \<circ> lp_prefix k) ` B = {}"
   and fixed_extra: "\<And>x. x\<in>\<Union>(vars_term ` set extra) \<Longrightarrow> x\<notin>p ` set V"
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
   and successor: "successor_goals = map (lp_cut_bind m (\<lambda>t. t\<cdot>(?s \<circ> lp_prefix k))) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. t\<cdot>?s)) gs"
   and result: "result = map (\<lambda>t. t\<cdot>?s) payload"
   using checked by (auto simp: lpc_no_return_resolve_def lpc_no_resolve_def lp_cut_short_goals_def o_def)
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
 have lengths: "length V = length images" using mgu by (simp add: lpc_check_mgu_def)
 have fixed: "map (\<lambda>t. t\<cdot>?cs) extra = extra"
   by (rule lpc_substitution_fixes_ambient_terms, rule lpc_conjugate_substitution_outside[OF inverse lengths], rule fixed_extra)
 note step = lpc_global_return_resolve_ambient[OF index global injective head_vars body_vars fresh_a fresh_goals fixed,
   of rest m saved]
 show ?thesis using step
   by (simp add: successor result map_map o_def lp_cut_map_comp lp_cut_map_bind
     lpc_conjugate_substitution_apply[OF inverse, unfolded o_def] lpc_conjugate_clause_update[OF inverse, unfolded o_def])
qed

ML \<open>
val checked = [@{thm lpc_no_return_resolve_renamed_ambient}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted renamed return resolution dependency" else ();
\<close>
end
