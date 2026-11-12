theory LP_Cut_NO_Return_Check
 imports LP_Cut_NO_Return_Attachment
begin

text \<open>A local NO witness reuses the existing checked resolution action,
adds freshness for the live return interface, and checks its exact update.
Saved frames and their answer rows are retained unchanged. This is not yet a
complete recurring-call certificate.\<close>

definition lpc_no_return_resolve where
 "lpc_no_return_resolve fuel P a gs c m saved payload k V images successor_goals result =
   (lpc_no_resolve fuel P a gs c m (map fst saved) k V images
      (LPCGoals successor_goals#map fst saved) \<and>
    lp_cut_short_goals k (map LPCAtom payload) \<and>
    result = map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images) payload)"

lemma lpc_no_return_resolve_attach_sound:
 fixes P :: "('f,string) lp_cut_program"
 assumes checked: "lpc_no_return_resolve fuel P a gs c m saved payload k V images successor_goals result"
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
   and successor_goals: "successor_goals = map (lp_cut_bind m (\<lambda>t. t\<cdot>(\<lambda>x. ?s (lp_prefix k x)))) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. t\<cdot>?s)) gs"
   and result: "result = map (\<lambda>t. t\<cdot>?s) payload"
   using checked by (auto simp: lpc_no_return_resolve_def lpc_no_resolve_def lp_cut_short_goals_def)
 have actual: "lpc_mgu_resolve (lp_ieval a LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs @
     map (\<lambda>t. LPCAtom (lp_ieval t LPIVar)) payload)
   (fst (P!c)) (snd (P!c))
   (\<lambda>x. lp_ieval (?s x) LPIVar)
   (\<lambda>x. lp_ieval (?s (lp_prefix k x)) LPIVar)"
   using lpc_checked_mgu_resolve[OF mgu short goals]
   by (simp add: map_map o_def)
 have answers: "lpc_return_env result LPIVar =
   (\<lambda>n. lp_isubst (lpc_return_env payload LPIVar n) (\<lambda>x. lp_ieval (?s x) LPIVar))"
   by (rule lpc_return_env_active)
     (simp add: result map_map o_def lp_ieval_finite_subst lp_ieval_subst)
 note step = lpc_return_resolve_attach[OF index actual,
   of rest m "lpc_return_eval LPIVar saved"]
 show ?thesis using step
   by (simp add: lpc_return_eval_def successor_goals answers map_map o_def
     lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

ML \<open>
val checked = [@{thm lpc_no_return_resolve_attach_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return-aware resolution check dependency" else ();
\<close>
end
