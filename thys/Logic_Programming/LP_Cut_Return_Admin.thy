theory LP_Cut_Return_Admin
  imports LP_Cut_Return_Source
begin

text \<open>Executable administrative transitions retain the environment of
each saved alternative. The outer option distinguishes an unsupported step
from a supported silent step; only an empty successful goal list emits a
return. Resolution and unification require separate checked obligations.\<close>

fun lpc_return_admin where
  "lpc_return_admin [] = None"
| "lpc_return_admin ((LPCBarrier m, eta)#es) = Some (None, es)"
| "lpc_return_admin ((LPCGoals [], eta)#es) = Some (Some eta, es)"
| "lpc_return_admin ((LPCGoals (LPCTrue#gs), eta)#es) =
    Some (None, (LPCGoals gs, eta)#es)"
| "lpc_return_admin ((LPCGoals (LPCFail#gs), eta)#es) = Some (None, es)"
| "lpc_return_admin ((LPCGoals (LPCCut m#gs), eta)#es) =
    Some (None, (LPCGoals gs, eta)#lpc_answer_prune m es)"
| "lpc_return_admin _ = None"

lemma lpc_return_admin_sound:
  "lpc_return_admin ss = Some (event, tt) \<Longrightarrow>
    lpc_answer_transition P ss event tt"
  by (induct ss rule: lpc_return_admin.induct)
    (auto intro: lpc_answer_transition.intros)

lemma lpc_return_admin_unique:
  assumes checked: "lpc_return_admin ss = Some (event, tt)"
    and step: "lpc_answer_transition P ss event' tt'"
  shows "event' = event \<and> tt' = tt"
  using step checked
  by (cases rule: lpc_answer_transition.cases) auto

text \<open>Finite symbolic frames can be checked before interpreting terms
and answer interfaces. Both maps use the same valuation; a saved alternative
must not be evaluated using the active frame's answer interface.\<close>

lemma lpc_answer_prune_map:
  "lpc_answer_prune m (map (map_prod (lp_cut_entry_map f) g) ss) =
    map (map_prod (lp_cut_entry_map f) g) (lpc_answer_prune m ss)"
  by (induct ss) (auto split: prod.splits lp_cut_entry.splits)

lemma lpc_return_admin_map:
  "lpc_return_admin (map (map_prod (lp_cut_entry_map f) g) ss) =
    map_option (map_prod (map_option g)
      (map (map_prod (lp_cut_entry_map f) g))) (lpc_return_admin ss)"
  by (induct ss rule: lpc_return_admin.induct)
    (simp_all add: lpc_answer_prune_map)

corollary lpc_return_admin_symbolic_sound:
  assumes "lpc_return_admin ss = Some (event, tt)"
  shows "lpc_answer_transition P
    (map (map_prod (lp_cut_entry_map f) g) ss) (map_option g event)
    (map (map_prod (lp_cut_entry_map f) g) tt)"
  by (rule lpc_return_admin_sound)
    (simp add: lpc_return_admin_map assms)

lemma lpc_return_admin_exhausted:
  "lpc_return_admin [] = None" by simp

lemma lpc_return_admin_success:
  "lpc_return_admin ((LPCGoals [], eta)#es) = Some (Some eta, es)" by simp

lemma lpc_return_admin_failure:
  "lpc_return_admin ((LPCGoals (LPCFail#gs), eta)#(e,nu)#es) =
    Some (None, (e,nu)#es)" by simp

lemma lpc_return_admin_cut:
  "lpc_return_admin [(LPCGoals [LPCCut m],eta), (LPCGoals gs,nu),
      (LPCBarrier m,rho), (LPCGoals rest,tau)] =
    Some (None, [(LPCGoals [],eta), (LPCBarrier m,rho), (LPCGoals rest,tau)])"
  by simp

lemma lpc_return_admin_empty_clause:
  "lpc_return_admin [(LPCClause [] c m,eta)] = None" by simp

lemma lpc_return_admin_unification_not_silent:
  "lpc_return_admin [(LPCGoals [LPCUnify a b],eta)] = None" by simp

end
