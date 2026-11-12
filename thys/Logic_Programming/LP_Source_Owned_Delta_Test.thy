theory LP_Source_Owned_Delta_Test
 imports LP_Source_Owned_Delta
begin

lemma delta_shared_scope_retained:
 "([LPCGoals [LPCCut 7,LPCCut 9],LPCBarrier 7] @ [LPCBarrier 9],
   [LPCGoals [LPCCut 9],LPCBarrier 7] @ [LPCBarrier 9]) \<in>lp_cut_mgu_source P"
proof (rule lpc_no_owned_delta_pending)
 show "([LPCGoals [LPCCut 7,LPCCut 9],LPCBarrier 7],
   [LPCGoals [LPCCut 9],LPCBarrier 7]) \<in>lp_cut_mgu_source P"
   by (rule lp_cut_mgu_source.admin) simp
qed simp_all

lemma delta_old_separation_too_strong:
 "(\<Union>e\<in>set [LPCGoals [LPCCut 9],LPCBarrier 7]. lp_cut_entry_scopes e)
   \<inter> (\<Union>e\<in>set [LPCBarrier 9]. lp_cut_entry_scopes e) \<noteq> {}"
 by simp

lemma delta_unowned_cut_rejected:
 "\<not> lpc_no_owned_suffix [LPCGoals [LPCCut 7,LPCCut 9]]"
 by simp

lemma delta_unowned_cut_discards_saved:
 "lp_cut_admin ([LPCGoals [LPCCut 7,LPCCut 9]] @ [LPCBarrier 9])
   \<noteq> Some ([LPCGoals [LPCCut 9]] @ [LPCBarrier 9])"
 by simp

lemma delta_new_scope_collision_rejected:
 "((\<Union>e\<in>set [LPCBarrier 7]. lp_cut_entry_scopes e) -
    (\<Union>e\<in>set [LPCGoals [LPCTrue]]. lp_cut_entry_scopes e)) \<inter>
    (\<Union>e\<in>set [LPCBarrier 7]. lp_cut_entry_scopes e) \<noteq> {}"
 by simp

ML \<open>
val checked = [@{thm delta_shared_scope_retained}, @{thm delta_old_separation_too_strong},
 @{thm delta_unowned_cut_rejected}, @{thm delta_unowned_cut_discards_saved},
 @{thm delta_new_scope_collision_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scope delta controls" else ();
\<close>
end
