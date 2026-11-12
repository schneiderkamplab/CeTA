theory LP_Prolog_NO_Scope_Permutation_Test
 imports LP_Prolog_NO_Scope_Permutation
begin

lemma scope_exchange_fresh:
 "lpc_exchange_support {7::nat} (\<lambda>n. n+10) ` {7} \<inter> {7,9} = {}"
 by (simp add: lpc_exchange_support_def)

lemma scope_exchange_restores_caller:
 "map (lp_cut_scope_goal (lpc_exchange_support {7::nat} (\<lambda>n. n+10)))
   (map (lp_cut_scope_goal (lpc_exchange_support {7::nat} (\<lambda>n. n+10)))
    [LPCCut 7,LPCCut 9]) = [LPCCut 7,LPCCut 9]"
 by (rule lpc_no_scope_restore_goals)
    (simp add: lpc_exchange_support_involution)

lemma scope_identity_collision_rejected:
 "\<not> (id ` {7::nat} \<inter> {7,9} = {})"
 by simp

lemma scope_one_way_shift_not_restoration:
 "map (lp_cut_scope_goal (\<lambda>n. n+10))
   (map (lp_cut_scope_goal (\<lambda>n. n+10)) [LPCCut 7]) \<noteq> [LPCCut 7]"
 by simp

ML \<open>
val checked = [@{thm scope_exchange_fresh}, @{thm scope_exchange_restores_caller},
 @{thm scope_identity_collision_rejected}, @{thm scope_one_way_shift_not_restoration}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scope controls" else ();
\<close>
end
