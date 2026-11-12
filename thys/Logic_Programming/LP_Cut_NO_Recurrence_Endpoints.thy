theory LP_Cut_NO_Recurrence_Endpoints
 imports LP_Prolog_NO_Trace_Scope_Support LP_Source_Call_Recurrence
begin

lemma lpc_no_scope_entry_map:
 "lp_cut_scope_entry r (lp_cut_entry_map f e) = lp_cut_entry_map f (lp_cut_scope_entry r e)"
 by (cases e) (simp_all add: map_map o_def lp_cut_scope_goal_map)

lemma lpc_no_scope_state_eval:
 "map (lp_cut_scope_entry r) (lp_cut_state_eval ss eta) =
   lp_cut_state_eval (map (lp_cut_scope_entry r) ss) eta"
 by (simp add: lp_cut_state_map_def map_map o_def lpc_no_scope_entry_map)

lemma lpc_no_return_initial_attachment:
 assumes fixed: "\<forall>x\<in>set vs. p x = x"
   and covered: "vars_term a \<subseteq> set vs"
   and observed: "map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env (map Var vs @ extra) LPIVar))) rest =
     map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
 shows "lpc_attach rest (lpc_return_eval LPIVar
    (lpc_no_rename_rows p extra [(LPCGoals [LPCAtom a],map Var vs)])) =
   lp_cut_state_eval [LPCGoals (LPCAtom a#gs)] LPIVar"
proof -
 have atom: "a\<cdot>(Var\<circ>p) = a"
   by (rule lpc_no_fixed_term_rename) (use covered fixed in auto)
 have coords: "map (\<lambda>t. t\<cdot>(Var\<circ>p)) (map Var vs) = map Var vs"
   using fixed by (induct vs) auto
 show ?thesis
   by (simp add: lpc_no_rename_rows_def lpc_return_eval_def atom coords[unfolded map_map]
     observed lp_cut_state_map_def)
qed

lemma lpc_no_return_final_attachment:
 assumes fixed: "\<forall>x\<in>vars_term b. p x = x"
 shows "\<exists>hs fs. map (lp_cut_scope_entry r)
   (lpc_attach rest (lpc_return_eval LPIVar
    (lpc_no_rename_rows p extra ((LPCGoals (LPCAtom b#pending),payload)#saved)))) @
     lp_cut_state_eval caller_saved LPIVar =
   lp_cut_state_eval (LPCGoals (LPCAtom b#hs)#fs) LPIVar"
proof -
 have atom: "b\<cdot>(Var\<circ>p) = b" by (rule lpc_no_fixed_term_rename[OF fixed])
 have finite: "map (lp_cut_scope_entry r)
   (lpc_attach rest (lpc_return_eval LPIVar
    (lpc_no_rename_rows p extra ((LPCGoals (LPCAtom b#pending),payload)#saved)))) @
     lp_cut_state_eval caller_saved LPIVar =
   lp_cut_state_eval (map (lp_cut_scope_entry r)
     (lpc_no_attach_finite rest (lpc_no_rename_rows p extra
       ((LPCGoals (LPCAtom b#pending),payload)#saved))) @ caller_saved) LPIVar"
   by (simp only: lpc_no_attach_finite_eval[symmetric] lpc_no_scope_state_eval)
      (simp add: lp_cut_state_map_def)
 show ?thesis
   unfolding finite
   by (simp add: lpc_no_rename_rows_def lpc_no_attach_finite_def atom; blast)
qed

ML \<open>
val checked = [@{thm lpc_no_scope_state_eval}, @{thm lpc_no_return_initial_attachment},
 @{thm lpc_no_return_final_attachment}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted recurrence endpoint reconstruction" else ();
\<close>
end
