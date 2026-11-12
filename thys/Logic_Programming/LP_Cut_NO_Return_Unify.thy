theory LP_Cut_NO_Return_Unify
 imports LP_Cut_NO_Return_Check
begin

lemma lpc_no_return_unify_attach_sound:
 assumes checked: "lpc_check_mgu fuel [(a,b)] V images"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCUnify a b#gs),payload)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images)) gs),
       map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images) payload)#saved)))"
proof -
 let ?s = "lpc_mgu_substitution V images"
 have actual: "lpc_mgu_unify (lp_ieval a LPIVar) (lp_ieval b LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs @
     map (\<lambda>t. LPCAtom (lp_ieval t LPIVar)) payload)
   (\<lambda>x. lp_ieval (?s x) LPIVar)"
   using lpc_checked_mgu_unify[OF checked, of "gs @ map LPCAtom payload"]
   by (simp add: map_map o_def)
 have answers: "lpc_return_env (map (\<lambda>t. t\<cdot>?s) payload) LPIVar =
   (\<lambda>n. lp_isubst (lpc_return_env payload LPIVar n) (\<lambda>x. lp_ieval (?s x) LPIVar))"
   by (rule lpc_return_env_active)
     (simp add: map_map o_def lp_ieval_finite_subst lp_ieval_subst)
 note step = lpc_return_unify_attach[OF actual, of P rest "lpc_return_eval LPIVar saved"]
 show ?thesis using step
   by (simp add: lpc_return_eval_def answers map_map o_def
     lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst)
qed

ML \<open>
val checked = [@{thm lpc_no_return_unify_attach_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return-aware unification dependency" else ();
\<close>
end
