theory LP_Prolog_Branch_Scope
  imports LP_Prolog_Branch_Builtin
begin

text \<open>The two fresh administrative scopes of a conditional branch may be
renamed independently. In particular, choosing the local scope must not identify
it with the commit scope. All original alternatives and their answer environments
are retained. This lemma does not discharge the invoked helper.\<close>

definition lpp_branch_stack where
  "lpp_branch_stack cs ys ns m n gs active saved =
    (LPCGoals (cs@[LPCCut m]@ys@gs),active)#(LPCBarrier n,active)#
    (LPCGoals (ns@gs),active)#(LPCBarrier m,active)#saved"

lemma lpp_branch_stack_scope:
  assumes plain: "list_all lpp_plain_goal (cs@ys@ns)"
  shows "lpc_return_scope r (lpp_branch_stack cs ys ns m n gs active saved) =
    lpp_branch_stack cs ys ns (r m) (r n) (map (lp_cut_scope_goal r) gs) active
      (lpc_return_scope r saved)"
  using plain by (simp add: lpp_branch_stack_def lpp_plain_goals_scope)

lemma lpp_branch_fresh_swap:
  assumes plain: "list_all lpp_plain_goal (cs@ys@ns)"
    and old: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and new: "lp_cut_fresh k (LPCGoals gs#map fst saved)"
  shows "lpc_return_scope (lp_cut_scope_swap m k)
      (lpp_branch_stack cs ys ns m n gs active saved) =
    lpp_branch_stack cs ys ns k (lp_cut_scope_swap m k n) gs active saved"
proof -
  have fixed: "map (lp_cut_scope_entry (lp_cut_scope_swap m k))
      (LPCGoals gs#map fst saved) = LPCGoals gs#map fst saved"
    by (rule lp_cut_fresh_swap_fixes[OF old new])
  have goals: "map (lp_cut_scope_goal (lp_cut_scope_swap m k)) gs=gs"
    and tail: "map (lp_cut_scope_entry (lp_cut_scope_swap m k)) (map fst saved)=map fst saved"
    using fixed by simp_all
  have saved: "lpc_return_scope (lp_cut_scope_swap m k) saved=saved"
    by (rule lpc_return_pairs_eq) (simp_all only: lpc_return_scope_erases tail lpc_return_scope_answers)
  show ?thesis by (simp add: lpp_branch_stack_scope[OF plain] goals saved lp_cut_scope_swap_def)
qed


lemma lpp_branch_fresh_local_swap:
  assumes plain: "list_all lpp_plain_goal (cs@ys@ns)"
    and old: "lp_cut_fresh n (LPCGoals gs#map fst saved)"
    and new: "lp_cut_fresh k (LPCGoals gs#map fst saved)"
    and separate: "m\<noteq>n" "m\<noteq>k"
  shows "lpc_return_scope (lp_cut_scope_swap n k)
      (lpp_branch_stack cs ys ns m n gs active saved) =
    lpp_branch_stack cs ys ns m k gs active saved"
proof -
  have fixed: "map (lp_cut_scope_entry (lp_cut_scope_swap n k))
      (LPCGoals gs#map fst saved) = LPCGoals gs#map fst saved"
    by (rule lp_cut_fresh_swap_fixes[OF old new])
  have goals: "map (lp_cut_scope_goal (lp_cut_scope_swap n k)) gs=gs"
    and tail: "map (lp_cut_scope_entry (lp_cut_scope_swap n k)) (map fst saved)=map fst saved"
    using fixed by simp_all
  have saved: "lpc_return_scope (lp_cut_scope_swap n k) saved=saved"
    by (rule lpc_return_pairs_eq) (simp_all only: lpc_return_scope_erases tail lpc_return_scope_answers)
  show ?thesis by (simp add: lpp_branch_stack_scope[OF plain] goals saved lp_cut_scope_swap_def separate)
qed

lemma lpp_branch_fresh_pair:
  assumes plain: "list_all lpp_plain_goal (cs@ys@ns)"
    and fm: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and fn: "lp_cut_fresh n (LPCGoals gs#map fst saved)"
    and fk: "lp_cut_fresh k (LPCGoals gs#map fst saved)"
    and fl: "lp_cut_fresh l (LPCGoals gs#map fst saved)"
    and distinct: "m\<noteq>n" "k\<noteq>l"
  shows "lpc_return_scope_word [(m,k),(lp_cut_scope_swap m k n,l)]
      (lpp_branch_stack cs ys ns m n gs active saved) =
    lpp_branch_stack cs ys ns k l gs active saved"
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
    by (simp only: lpc_return_scope_word.simps lpp_branch_fresh_swap[OF plain fm fk]
      lpp_branch_fresh_local_swap[OF plain fresh fl different distinct(2)])
qed

end
