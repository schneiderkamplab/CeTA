theory LP_Cut_NO_Renamed_Unify
 imports LP_Cut_NO_Swap_Support LP_Cut_NO_Return_Unify
begin

lemma lpc_global_return_unify_ambient:
 assumes mgu: "lpc_global_mgu [(a,b)] substitution"
   and fixed: "map (\<lambda>t. t\<cdot>substitution) extra = extra"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCUnify a b#gs),payload@extra)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>substitution)) gs),
       map (\<lambda>t. t\<cdot>substitution) payload @ extra)#saved)))"
proof -
 have actual: "lpc_mgu_unify (lp_ieval a LPIVar) (lp_ieval b LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs @
     map (\<lambda>t. LPCAtom (lp_ieval t LPIVar)) (payload@extra))
   (\<lambda>x. lp_ieval (substitution x) LPIVar)"
   using lpc_global_mgu_unify[OF mgu, of "gs @ map LPCAtom (payload@extra)"]
   by (simp add: map_map o_def)
 note answers = lpc_return_ambient_update[OF refl fixed, of payload]
 note step = lpc_return_unify_attach[OF actual, of P rest "lpc_return_eval LPIVar saved"]
 show ?thesis using step by (simp add: lpc_return_eval_def answers map_map o_def
   lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst)
qed

lemma lpc_no_return_unify_renamed_ambient:
 assumes checked: "lpc_check_mgu fuel [(a,b)] V images"
   and inverse: "\<And>x. p (p x) = x"
   and outside: "\<And>x. x\<in>\<Union>(vars_term ` set extra) \<Longrightarrow> x\<notin>p ` set V"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCUnify (a\<cdot>(Var \<circ> p)) (b\<cdot>(Var \<circ> p))#
       map (lp_cut_map (\<lambda>t. t\<cdot>(Var \<circ> p))) gs),
       map (\<lambda>t. t\<cdot>(Var \<circ> p)) payload @ extra)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_map (\<lambda>t. (t\<cdot>lpc_mgu_substitution V images)\<cdot>(Var \<circ> p))) gs),
       map (\<lambda>t. (t\<cdot>lpc_mgu_substitution V images)\<cdot>(Var \<circ> p)) payload @ extra)#saved)))"
proof -
 let ?cs = "lpc_conjugate_substitution p (lpc_mgu_substitution V images)"
 have global: "lpc_global_mgu [(a\<cdot>(Var \<circ> p),b\<cdot>(Var \<circ> p))] ?cs"
   using lpc_global_mgu_conjugate[OF lpc_checked_global_mgu[OF checked] inverse]
   by (simp add: lpc_rename_equations_def)
 have lengths: "length V=length images" using checked by (simp add: lpc_check_mgu_def)
 have fixed: "map (\<lambda>t. t\<cdot>?cs) extra = extra"
   by (rule lpc_substitution_fixes_ambient_terms,
     rule lpc_conjugate_substitution_outside[OF inverse lengths], rule outside)
 note step = lpc_global_return_unify_ambient[OF global fixed,
   of P rest "map (lp_cut_map (\<lambda>t. t\<cdot>(Var \<circ> p))) gs"
     "map (\<lambda>t. t\<cdot>(Var \<circ> p)) payload" saved]
 show ?thesis using step by (simp add: map_map o_def lp_cut_map_comp
   lpc_conjugate_substitution_apply[OF inverse, unfolded o_def])
qed

ML \<open>
val checked = [@{thm lpc_global_return_unify_ambient}, @{thm lpc_no_return_unify_renamed_ambient}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted renamed return unification" else ();
\<close>
end
