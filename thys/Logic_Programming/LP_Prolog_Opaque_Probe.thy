theory LP_Prolog_Opaque_Probe
  imports LP_Prolog_Return_Check
begin

text \<open>The two fresh administrative scopes of an opaque probe may be
renamed independently. In particular, choosing the local scope must not identify
it with the commit scope. All original alternatives and their answer environments
are retained. This lemma does not discharge the invoked helper.\<close>

definition lpp_probe_stack where
  "lpp_probe_stack a keep m n gs active saved =
    (LPCGoals (lpp_probe_goals a keep m gs),active)#(LPCBarrier n,active)#
    (LPCGoals (lpp_probe_else keep gs),active)#(LPCBarrier m,active)#saved"

lemma lpp_probe_stack_scope:
  "lpc_return_scope r (lpp_probe_stack a keep m n gs active saved) =
    lpp_probe_stack a keep (r m) (r n) (map (lp_cut_scope_goal r) gs) active
      (lpc_return_scope r saved)"
  by (simp add: lpp_probe_stack_def lpp_probe_goals_def lpp_probe_else_def)

lemma lpp_probe_fresh_swap:
  assumes old: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and new: "lp_cut_fresh k (LPCGoals gs#map fst saved)"
  shows "lpc_return_scope (lp_cut_scope_swap m k)
      (lpp_probe_stack a keep m n gs active saved) =
    lpp_probe_stack a keep k (lp_cut_scope_swap m k n) gs active saved"
proof -
  have fixed: "map (lp_cut_scope_entry (lp_cut_scope_swap m k))
      (LPCGoals gs#map fst saved) = LPCGoals gs#map fst saved"
    by (rule lp_cut_fresh_swap_fixes[OF old new])
  have goals: "map (lp_cut_scope_goal (lp_cut_scope_swap m k)) gs=gs"
    and tail: "map (lp_cut_scope_entry (lp_cut_scope_swap m k)) (map fst saved)=map fst saved"
    using fixed by simp_all
  have saved: "lpc_return_scope (lp_cut_scope_swap m k) saved=saved"
    by (rule lpc_return_pairs_eq) (simp_all only: lpc_return_scope_erases tail lpc_return_scope_answers)
  show ?thesis by (simp add: lpp_probe_stack_scope goals saved lp_cut_scope_swap_def)
qed


lemma lpp_probe_fresh_local_swap:
  assumes old: "lp_cut_fresh n (LPCGoals gs#map fst saved)"
    and new: "lp_cut_fresh k (LPCGoals gs#map fst saved)"
    and separate: "m\<noteq>n" "m\<noteq>k"
  shows "lpc_return_scope (lp_cut_scope_swap n k)
      (lpp_probe_stack a keep m n gs active saved) =
    lpp_probe_stack a keep m k gs active saved"
proof -
  have fixed: "map (lp_cut_scope_entry (lp_cut_scope_swap n k))
      (LPCGoals gs#map fst saved) = LPCGoals gs#map fst saved"
    by (rule lp_cut_fresh_swap_fixes[OF old new])
  have goals: "map (lp_cut_scope_goal (lp_cut_scope_swap n k)) gs=gs"
    and tail: "map (lp_cut_scope_entry (lp_cut_scope_swap n k)) (map fst saved)=map fst saved"
    using fixed by simp_all
  have saved: "lpc_return_scope (lp_cut_scope_swap n k) saved=saved"
    by (rule lpc_return_pairs_eq) (simp_all only: lpc_return_scope_erases tail lpc_return_scope_answers)
  show ?thesis by (simp add: lpp_probe_stack_scope goals saved lp_cut_scope_swap_def separate)
qed

lemma lpp_probe_fresh_pair:
  assumes fm: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and fn: "lp_cut_fresh n (LPCGoals gs#map fst saved)"
    and fk: "lp_cut_fresh k (LPCGoals gs#map fst saved)"
    and fl: "lp_cut_fresh l (LPCGoals gs#map fst saved)"
    and distinct: "m\<noteq>n" "k\<noteq>l"
  shows "lpc_return_scope_word [(m,k),(lp_cut_scope_swap m k n,l)]
      (lpp_probe_stack a keep m n gs active saved) =
    lpp_probe_stack a keep k l gs active saved"
proof -
  let ?r = "lp_cut_scope_swap m k"
  have fixed: "map (lp_cut_scope_entry ?r) (LPCGoals gs#map fst saved) =
      LPCGoals gs#map fst saved"
    by (rule lp_cut_fresh_swap_fixes[OF fm fk])
  have fresh: "lp_cut_fresh (?r n) (LPCGoals gs#map fst saved)"
    using lp_cut_scope_fresh[OF lp_cut_scope_swap_injective[of m k], where m=n and es="LPCGoals gs#map fst saved"] fn by (simp only: fixed)
  have different: "k\<noteq>?r n"
    using distinct(1) by (auto simp: lp_cut_scope_swap_def)
  show ?thesis
    by (simp only: lpc_return_scope_word.simps lpp_probe_fresh_swap[OF fm fk]
      lpp_probe_fresh_local_swap[OF fresh fl different distinct(2)])
qed

end
