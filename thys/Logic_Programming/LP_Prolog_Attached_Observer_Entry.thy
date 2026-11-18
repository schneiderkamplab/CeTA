theory LP_Prolog_Attached_Observer_Entry
 imports LP_Prolog_Checked_Attached_Leaf_Link
begin

text \<open>Module entry instantiates executable goals while retaining an
independent caller environment. The caller need not occur in the helper's
local payload or substitution domain. No return property is obtained from
entry equality; a contract for the attached execution is still required.\<close>

lemma lpp_checked_observer_entry_state:
 fixes eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes checked: "lp_cut_check_instance [LPCGoals caller_goals] G guards
   [LPCGoals helper_goals] H helper_guards bindings []"
 defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta"
 shows "lpc_attach_answers rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) caller_goals),ret)#saved) =
   lpc_attach_answers rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t nu)) helper_goals),ret)#saved)"
proof -
 have shape: "[LPCGoals caller_goals] =
   lp_cut_state_map (\<lambda>t. t\<cdot>lp_cut_instance_subst bindings) [LPCGoals helper_goals]"
  using checked by (simp add: lp_cut_check_instance_def Let_def)
 have evaluated: "lp_cut_state_eval [LPCGoals caller_goals] eta =
   lp_cut_state_eval [LPCGoals helper_goals] nu"
  using arg_cong[OF shape, of "\<lambda>s. lp_cut_state_eval s eta"]
  by (simp add: lp_cut_state_eval_subst nu_def)
 have same: "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) caller_goals =
   map (lp_cut_map (\<lambda>t. lp_ieval t nu)) helper_goals"
  using evaluated by (simp add: lp_cut_state_map_def)
 show ?thesis by (simp only: same)
qed

lemma lpp_checked_observer_entry_contract:
 fixes eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes checked: "lp_cut_check_instance [LPCGoals caller_goals] G guards
   [LPCGoals helper_goals] H helper_guards bindings []"
 and known: "lp_cut_knowledge (set G) guards eta"
 and helper: "\<And>nu. lp_cut_knowledge (set H) helper_guards nu \<Longrightarrow>
   lp_answer_contract T
    (lpc_attach_answers rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t nu)) helper_goals),ret)#saved))
    R subject returned"
 shows "lp_answer_contract T
   (lpc_attach_answers rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) caller_goals),ret)#saved))
   R subject returned"
proof -
 let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta"
 have child_known: "lp_cut_knowledge (set H) helper_guards ?nu"
  by (rule lp_cut_checked_instance_knowledge[OF checked known])
 have equal: "lpc_attach_answers rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) caller_goals),ret)#saved) =
   lpc_attach_answers rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t ?nu)) helper_goals),ret)#saved)"
  using lpp_checked_observer_entry_state[OF checked] by blast
 show ?thesis using helper[OF child_known] by (simp only: equal)
qed

ML \<open>
val checked = @{thms lpp_checked_observer_entry_state lpp_checked_observer_entry_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached observer entry" else ();
\<close>
end
