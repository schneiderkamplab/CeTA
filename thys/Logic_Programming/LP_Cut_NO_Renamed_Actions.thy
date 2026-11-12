theory LP_Cut_NO_Renamed_Actions
 imports LP_Cut_NO_Action_Support
begin

lemma lpc_no_fresh_finite_support:
 fixes A S C :: "string set"
 assumes finite: "finite A" "finite S" "finite C"
   and separate: "A \<inter> C = {}"
 shows "\<exists>p. (\<forall>z. p (p z) = z) \<and> (\<forall>z\<in>A. p z = z) \<and> C \<inter> p ` S = {}"
proof -
 have private_finite: "finite (S-A)" using finite by simp
 have private_disjoint: "A \<inter> (S-A) = {}" by blast
 obtain p :: "string \<Rightarrow> string" where inverse: "\<forall>z. p (p z) = z"
   and fixed: "\<forall>z\<in>A. p z = z"
   and moved: "p ` (S-A) \<inter> (A \<union> (S-A) \<union> C) = {}"
   using lpc_fresh_private_involution[OF finite(1) private_finite finite(3) private_disjoint]
   by (elim exE conjE) assumption
 have outside: "p z\<notin>C" if member: "z\<in>S" for z
 proof (cases "z\<in>A")
   case True
   have equal: "p z = z" using fixed True by blast
   show ?thesis using separate True by (auto simp: equal)
 next
   case False
   have member_private: "z\<in>S-A" using member False by simp
   have image: "p z\<in>p ` (S-A)" by (rule imageI[OF member_private])
   show ?thesis using moved image by blast
 qed
 have disjoint: "C \<inter> p ` S = {}" using outside by auto
 show ?thesis
 proof (rule exI[of _ p], intro conjI)
   show "\<forall>z. p (p z) = z" by (rule inverse)
   show "\<forall>z\<in>A. p z = z" by (rule fixed)
   show "C \<inter> p ` S = {}" by (rule disjoint)
 qed
qed

lemma lpc_no_resolve_rows_renamed:
 assumes checked: "lpc_no_return_resolve fuel P a gs c m saved payload k V images hs result"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "lpc_no_return_rename_safe P p extra (LPCNOResolve k V images)"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCClause (LPCAtom a#gs) c m,payload)#saved)))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCGoals hs,result)#saved))))"
proof -
 have index: "c<length P" using checked
   by (simp add: lpc_no_return_resolve_def lpc_no_resolve_def)
 have fresh: "vars_term t \<inter> (p \<circ> lp_prefix k) ` lpc_no_program_vars P = {}"
   if "t\<in>set extra" for t
   by (rule lpc_no_return_rename_safe_fresh[OF safe _ that]) simp
 have fixed: "x\<notin>p ` set V" if "x\<in>\<Union>(vars_term ` set extra)" for x
   by (rule lpc_no_return_rename_safe_subset[OF safe _ that]) simp
 note step = lpc_no_return_resolve_renamed_ambient[where rest=rest and extra=extra and saved="lpc_no_rename_rows p extra saved",
   OF checked inverse
   lpc_no_program_head_vars[OF index] lpc_no_program_body_vars[OF index] fresh fixed]
 show ?thesis using step by (simp add: lpc_no_rename_rows_def)
qed

lemma lpc_no_swap_rows_renamed:
 assumes checked: "lpc_no_return_resolve_swap fuel P a gs c m saved payload k V images x y hs result"
   and inverse: "\<And>z. p (p z) = z"
   and safe: "lpc_no_return_rename_safe P p extra (LPCNOResolveSwap k V images x y)"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCClause (LPCAtom a#gs) c m,payload)#saved)))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCGoals hs,result)#saved))))"
proof -
 have index: "c<length P" and lengths: "length V=length images" using checked
   by (auto simp: lpc_no_return_resolve_swap_def lpc_no_resolve_swap_def lpc_check_mgu_def)
 have fresh: "vars_term t \<inter> (p \<circ> lp_prefix k) ` lpc_no_program_vars P = {}"
   if "t\<in>set extra" for t
   by (rule lpc_no_return_rename_safe_fresh[OF safe _ that]) auto
 have outside: "z\<notin>p ` (set V \<union> {x,y})"
   if "z\<in>\<Union>(vars_term ` set extra)" for z
   by (rule lpc_no_return_rename_safe_subset[OF safe _ that]) auto
 have fixed: "map (\<lambda>t. (t\<cdot>lpc_conjugate_substitution p (lpc_mgu_substitution V images))\<cdot>
     (\<lambda>v. Var (lpc_no_swap (p x) (p y) v))) extra = extra"
   by (rule lpc_renamed_swap_fixes_ambient[OF inverse lengths outside])
 note step = lpc_no_return_swap_renamed_ambient[where rest=rest and extra=extra and saved="lpc_no_rename_rows p extra saved",
   OF checked inverse
   lpc_no_program_head_vars[OF index] lpc_no_program_body_vars[OF index] fresh fixed]
 show ?thesis using step by (simp add: lpc_no_rename_rows_def)
qed

lemma lpc_no_unify_rows_renamed:
 assumes checked: "lpc_check_mgu fuel [(a,b)] V images"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "lpc_no_return_rename_safe P p extra (LPCNOUnify V images)"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCGoals (LPCUnify a b#gs),payload)#saved)))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra
       ((LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images)) gs),
         map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images) payload)#saved))))"
proof -
 have outside: "x\<notin>p ` set V" if "x\<in>\<Union>(vars_term ` set extra)" for x
   by (rule lpc_no_return_rename_safe_subset[OF safe _ that]) simp
 note step = lpc_no_return_unify_renamed_ambient[where P=P and rest=rest and gs=gs and payload=payload
   and extra=extra and saved="lpc_no_rename_rows p extra saved", OF checked inverse outside]
 show ?thesis using step by (simp add: lpc_no_rename_rows_def map_map o_def lp_cut_map_comp)
qed

lemma lpc_no_case_rows_renamed:
 assumes fresh: "lp_cut_fresh m (LPCGoals (LPCAtom (Fun (LPCUser f) call_args)#gs)#map fst saved)"
   and separated: "m\<notin>lpc_rest_scopes rest"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCGoals (LPCAtom (Fun (LPCUser f) call_args)#gs),payload)#saved)))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra
       (map (\<lambda>c. (LPCClause (LPCAtom (Fun (LPCUser f) call_args)#gs) c m,payload))
         (lp_cut_slice P (LPCUser f) (length call_args)) @ (LPCBarrier m,payload)#saved))))"
proof -
 let ?r = "\<lambda>t. t\<cdot>(Var \<circ> p)"
 have renamed_fresh: "lp_cut_fresh m
   (LPCGoals (LPCAtom (Fun (LPCUser f) (map ?r call_args))#map (lp_cut_map ?r) gs)#
     map fst (lpc_no_rename_rows p extra saved))"
   using fresh by (simp add: lpc_no_rename_rows_erases lp_cut_state_map_def lp_cut_fresh_def)
 note step = lpc_no_return_case_attach_sound[where P=P and payload="map ?r payload @ extra", OF renamed_fresh separated]
 show ?thesis using step by (simp add: lpc_no_rename_rows_def map_map o_def)
qed

ML \<open>
val checked = [@{thm lpc_no_fresh_finite_support}, @{thm lpc_no_resolve_rows_renamed}, @{thm lpc_no_swap_rows_renamed},
 @{thm lpc_no_unify_rows_renamed}, @{thm lpc_no_case_rows_renamed}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted uniform renamed NO actions" else ();
\<close>
end
