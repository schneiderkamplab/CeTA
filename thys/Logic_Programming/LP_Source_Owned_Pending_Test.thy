theory LP_Source_Owned_Pending_Test
 imports LP_Source_Owned_Pending
begin

lemma owned_cut_keeps_caller:
 "lp_cut_admin ([LPCGoals [LPCCut 7],LPCGoals [LPCFail],LPCBarrier 7] @
   [LPCGoals [LPCTrue],LPCBarrier 0]) =
   Some ([LPCGoals [],LPCBarrier 7] @ [LPCGoals [LPCTrue],LPCBarrier 0])"
 by simp

lemma owned_cut_rejects_missing_barrier:
 "\<not> lpc_no_owned_suffix [LPCGoals [LPCCut 7],LPCBarrier 3]"
 by simp

lemma unowned_cut_drops_caller:
 "lp_cut_admin ([LPCGoals [LPCCut 7]] @ [LPCGoals [LPCTrue]]) \<noteq>
   Some ([LPCGoals []] @ [LPCGoals [LPCTrue]])"
 by simp

lemma noninjective_scope_map_fakes_ownership:
 "\<not> lpc_no_owned_suffix [LPCGoals [LPCCut 7],LPCBarrier 3] \<and>
   lpc_no_owned_suffix (map (lp_cut_scope_entry (\<lambda>m. 0))
     [LPCGoals [LPCCut 7],LPCBarrier 3])"
 by simp

lemma owned_cut_keeps_saved_answer_rows:
 "lpc_return_admin
   ([(LPCGoals [LPCCut 7],[''active'']), (LPCGoals [LPCFail],[''discard'']),
      (LPCBarrier 7,[''barrier''])] @ [(LPCGoals [LPCTrue],[''caller''])]) =
   Some (None,[(LPCGoals [],[''active'']),(LPCBarrier 7,[''barrier'']),
     (LPCGoals [LPCTrue],[''caller''])])"
 by simp

ML \<open>
val checked = [@{thm owned_cut_keeps_caller}, @{thm owned_cut_rejects_missing_barrier},
 @{thm unowned_cut_drops_caller}, @{thm noninjective_scope_map_fakes_ownership},
 @{thm owned_cut_keeps_saved_answer_rows}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted owned cut regressions" else ();
\<close>
end
