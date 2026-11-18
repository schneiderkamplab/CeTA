theory LP_Prolog_Observer_Rebase_Entry
 imports LP_Prolog_Observer_Module_Link
begin

lemma lpp_observer_rebase_entry_representation:
 assumes shape: "runtime=[(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),env)]"
 shows "lpc_reinterface (\<lambda>env x. env (Inl x))
   (lpp_observer_rebase (\<lambda>_ _. lpc_return_env helper_payload eta) runtime) =
  lpc_return_eval eta [(LPCGoals gs,helper_payload)]"
 by (simp add: shape lpp_observer_rebase_helper lpc_return_eval_def)

lemma lpp_observer_rebase_does_not_merge_saved:
 assumes different: "caller x\<noteq>saved_caller x"
 shows "(snd (hd (lpp_observer_rebase helper
    [(active_entry,case_sum helper_env caller),(saved_entry,case_sum saved_helper saved_caller)]))) (Inr x)
  \<noteq> (snd (last (lpp_observer_rebase helper
    [(active_entry,case_sum helper_env caller),(saved_entry,case_sum saved_helper saved_caller)]))) (Inr x)"
 using different by (simp add: lpp_observer_rebase_def)

lemma lpp_observer_rebase_preserves_alias:
 "(snd (hd (lpp_observer_rebase (\<lambda>_ _. helper_env) [(frame_entry,case_sum old_helper caller)]))) (Inl x) =
   (snd (hd (lpp_observer_rebase (\<lambda>_ _. helper_env) [(frame_entry,case_sum old_helper caller)]))) (Inr y)
  \<longleftrightarrow> helper_env x=caller y"
 by (simp add: lpp_observer_rebase_def)

lemma lpp_observer_nonempty_boundary_contract:
 assumes boundary: "states!i\<noteq>[] \<Longrightarrow>
  lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts node_conditions J rest returned i"
 shows "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts node_conditions J rest returned i"
 by (cases "states!i=[]") (use lpp_observer_empty_node_contract boundary in auto)

end
