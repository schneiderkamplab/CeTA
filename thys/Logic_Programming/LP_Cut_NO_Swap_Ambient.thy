theory LP_Cut_NO_Swap_Ambient
 imports LP_Cut_NO_Renamed_Return LP_Cut_NO_Return_Swap
begin

text \<open>Output swaps preserve semantic most-generality, while their composed
substitution must fix the extra caller coordinates. The stronger solved-form
global MGU predicate is used before the swap, not asserted after it.\<close>

lemma lpc_global_return_resolve_swap_ambient:
 fixes P :: "('f,string) lp_cut_program"
 assumes index: "c<length P"
   and mgu: "lpc_global_mgu [(a,fst (P!c)\<cdot>(Var \<circ> rename_clause_var))] substitution"
   and injective: "inj_on rename_clause_var B"
   and head_vars: "vars_term (fst (P!c)) \<subseteq> B"
   and body_vars: "\<forall>g\<in>set (snd (P!c)). \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> B"
   and fresh_a: "vars_term a \<inter> rename_clause_var ` B = {}"
   and fresh_goals: "\<forall>g\<in>set (gs @ map LPCAtom (payload@extra)). \<forall>t\<in>set (lp_cut_terms g).
     vars_term t \<inter> rename_clause_var ` B = {}"
   and fixed: "map (\<lambda>t. (t\<cdot>substitution)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v))) extra = extra"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCClause (LPCAtom a#gs) c m,payload@extra)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_bind m (\<lambda>t. (t\<cdot>(substitution \<circ> rename_clause_var))\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. (t\<cdot>substitution)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) gs),
       map (\<lambda>t. (t\<cdot>substitution)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v))) payload @ extra)#saved)))"
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
   (map (\<lambda>t. (t\<cdot>substitution)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v))) payload @ extra) LPIVar =
   (\<lambda>n. lp_isubst (lpc_return_env (payload@extra) LPIVar n)
     (\<lambda>v. lp_isubst (lp_ieval (substitution v) LPIVar) (\<lambda>w. LPIVar (lpc_no_swap x y w))))"
   apply (rule lpc_return_env_active)
   using arg_cong[OF fixed, of "map (\<lambda>t. lp_ieval t LPIVar)"]
   by (simp add: map_map o_def lp_ieval_finite_subst lp_ieval_subst)
 note swapped = lpc_mgu_resolve_output_swap[OF actual, of x y]
 note step = lpc_return_resolve_attach[OF index swapped,
   of rest m "lpc_return_eval LPIVar saved"]
 show ?thesis using step
   by (simp add: lpc_return_eval_def answers map_map o_def
     lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

ML \<open>
val checked = [@{thm lpc_global_return_resolve_swap_ambient}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted ambient output swap dependency" else ();
\<close>
end
