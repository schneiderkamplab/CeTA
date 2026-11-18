theory LP_Prolog_Observer_Rebase
 imports LP_Prolog_Observer_Frontier_Link_Contracts LP_Prolog_Observer_Frontier_Module
begin

text \<open>Changing a module's helper observation leaves the actual caller
execution unchanged, including every saved environment. The new helper
representation is a separate checked obligation; rebasing supplies no facts.\<close>

definition lpp_observer_rebase where
 "lpp_observer_rebase helper runtime = map (\<lambda>(frame_entry,env).
   (frame_entry,case_sum (helper frame_entry env) (\<lambda>x. env (Inr x)))) runtime"

lemma lpp_observer_rebase_caller:
 "lpc_reinterface (\<lambda>env x. env (Inr x)) (lpp_observer_rebase helper runtime) =
  lpc_reinterface (\<lambda>env x. env (Inr x)) runtime"
 by (simp add: lpp_observer_rebase_def lpc_reinterface_def case_prod_unfold)

lemma lpp_observer_rebase_helper:
 "lpc_reinterface (\<lambda>env x. env (Inl x)) (lpp_observer_rebase helper runtime) =
  map (\<lambda>(frame_entry,env). (frame_entry,helper frame_entry env)) runtime"
 by (simp add: lpp_observer_rebase_def lpc_reinterface_def case_prod_unfold)

lemma lpp_observer_rebase_invariant:
 "lpp_observer_invariant A specs rest (lpp_observer_rebase helper runtime) =
  lpp_observer_invariant A specs rest runtime"
 by (simp add: lpp_observer_invariant_def lpp_observer_rebase_caller)

lemma lpp_observer_rebase_answer_contract:
 "lp_answer_contract T
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpp_observer_rebase helper runtime))) R subject returned =
  lp_answer_contract T
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
 by (simp add: lpp_observer_rebase_caller)

lemma lpp_observer_rebase_singleton:
 "lpp_observer_rebase (\<lambda>_ _. helper_env) [(frame_entry,env)] =
   [(frame_entry,case_sum helper_env (\<lambda>x. env (Inr x)))]"
 by (simp add: lpp_observer_rebase_def)

lemma lpp_observer_rebase_saved_environments:
 "map snd (lpc_reinterface (\<lambda>env x. env (Inr x))
   (lpp_observer_rebase helper (active@ saved))) =
  map snd (lpc_reinterface (\<lambda>env x. env (Inr x)) (active@ saved))"
 by (simp add: lpp_observer_rebase_caller)

end
