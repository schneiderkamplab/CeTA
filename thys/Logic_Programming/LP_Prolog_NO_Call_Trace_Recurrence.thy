theory LP_Prolog_NO_Call_Trace_Recurrence
 imports LP_Cut_NO_Recurrence_Endpoints
begin

lemma lpc_no_scope_goals_map:
 "map (lp_cut_map f) (map (lp_cut_scope_goal r) gs) =
  map (lp_cut_scope_goal r) (map (lp_cut_map f) gs)"
 by (simp add: map_map o_def lp_cut_scope_goal_map)

lemma lpp_no_call_trace_repeat:
 fixes a b :: "(string lp_cut_symbol,string) term"
 assumes checked: "lpp_no_return_trace fuel P reserved
    [(LPCGoals [LPCAtom a],map Var vs)] steps
    ((LPCGoals (LPCAtom b#pending),payload)#saved)"
   and boundaries: "lpp_no_return_boundaries [(LPCGoals [LPCAtom a],map Var vs)] steps"
   and nonempty: "steps\<noteq>[]"
   and distinct: "distinct vs"
   and cover: "vars_term a \<subseteq> set vs" "vars_term b \<subseteq> set vs"
   and program: "lp_cut_source_program P"
 shows "\<exists>hs fs. (lp_cut_state_eval (LPCGoals (LPCAtom a#gs)#es) LPIVar,
   lp_cut_state_eval (LPCGoals (LPCAtom b#hs)#fs) LPIVar)
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?start = "[(LPCGoals [LPCAtom a],map Var vs)]"
 let ?finish = "((LPCGoals (LPCAtom b#pending),payload)#saved)"
 obtain extra where extra_distinct: "distinct (vs@extra)"
   and extra_separate: "set extra \<inter> set vs = {}"
   and extra_cover: "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> set (vs@extra)"
   and observation: "map (lp_cut_map (\<lambda>t. lp_ieval (lpc_seg_position_template (vs@extra) t)
     (lpc_return_env (map Var vs @ map Var extra) LPIVar))) gs =
     map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
   using lpc_return_context_template[OF distinct, of gs] by (elim exE conjE) assumption
 let ?rest = "map (lp_cut_map (lpc_seg_position_template (vs@extra))) gs"
 have observed: "map (lp_cut_map (\<lambda>t. lp_ieval t
   (lpc_return_env (map Var vs @ map Var extra) LPIVar))) ?rest =
   map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
   using observation by (simp add: map_map o_def lp_cut_map_comp)
 let ?V = "lpp_no_return_trace_support P ?start steps"
 have separate: "set vs \<inter> set extra = {}" using extra_separate by auto
 obtain p where inverse_p: "\<forall>x. p (p x) = x"
   and fixed_p: "\<forall>x\<in>set vs. p x = x"
   and disjoint_p: "set extra \<inter> p ` ?V = {}"
   using lpc_no_fresh_finite_support[where A="set vs" and S="?V" and C="set extra",
     OF finite_set lpp_no_return_trace_support_finite finite_set separate]
   by (elim exE conjE) assumption
 have safe: "(\<Union>t\<in>set (map Var extra). vars_term t) \<inter> p ` ?V = {}"
   using disjoint_p by simp
 let ?S = "lpp_no_trace_scope_support steps"
 let ?E = "(\<Union>e\<in>set (LPCGoals gs#es). lp_cut_entry_scopes e)"
 obtain r where inverse_r: "\<forall>x. r (r x) = x" and bij_r: "bij r"
   and disjoint_r: "r ` ?S \<inter> ?E = {}"
   using lpc_no_fresh_scope_permutation[where S="?S" and E="?E",
     OF lpp_no_trace_scope_support_finite lpc_no_scopes_finite]
   by (elim exE conjE) assumption
 have injective: "inj r" using bij_r by (simp add: bij_def)
 have rest_separate: "r ` ?S \<inter> lpc_rest_scopes ?rest = {}"
   using disjoint_r by auto
 have saved_separate: "r ` ?S \<inter>
   (\<Union>e\<in>set (lp_cut_state_eval es LPIVar). lp_cut_entry_scopes e) = {}"
   using disjoint_r by (auto simp: lp_cut_state_map_def)
 let ?pre = "map (lp_cut_scope_goal r) ?rest"
 have scopes: "\<forall>action\<in>set (map fst steps). lpp_no_action_scope_safe ?pre action"
   by (rule lpp_no_trace_scope_preimage_safe[OF inverse_r rest_separate])
 have path: "(map (lp_cut_scope_entry r)
   (lpc_attach ?pre (lpc_return_eval LPIVar (lpc_no_rename_rows p (map Var extra) ?start))) @
    lp_cut_state_eval es LPIVar,
   map (lp_cut_scope_entry r)
   (lpc_attach ?pre (lpc_return_eval LPIVar (lpc_no_rename_rows p (map Var extra) ?finish))) @
    lp_cut_state_eval es LPIVar)
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   by (rule lpp_no_return_trace_saved_progress[OF checked _ safe boundaries
     lpp_no_trace_scope_support_targets scopes nonempty injective program saved_separate])
      (use inverse_p in auto)
 have pre_observed: "map (lp_cut_map (\<lambda>t. lp_ieval t
   (lpc_return_env (map Var vs @ map Var extra) LPIVar))) ?pre =
   map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) (map (lp_cut_scope_goal r) gs)"
   by (simp only: lpc_no_scope_goals_map observed)
 have restore_goal: "lp_cut_scope_goal r (lp_cut_scope_goal r g) = g" for g
   by (cases g) (simp_all add: inverse_r)
 have initial: "map (lp_cut_scope_entry r)
   (lpc_attach ?pre (lpc_return_eval LPIVar (lpc_no_rename_rows p (map Var extra) ?start))) @
    lp_cut_state_eval es LPIVar = lp_cut_state_eval (LPCGoals (LPCAtom a#gs)#es) LPIVar"
   by (simp only: lpc_no_return_initial_attachment[OF fixed_p cover(1) pre_observed]
      lpc_no_scope_state_eval)
      (simp add: lp_cut_state_map_def restore_goal)
 have fixed_b: "\<forall>x\<in>vars_term b. p x = x" using cover(2) fixed_p by auto
 obtain hs fs where final: "map (lp_cut_scope_entry r)
   (lpc_attach ?pre (lpc_return_eval LPIVar (lpc_no_rename_rows p (map Var extra) ?finish))) @
    lp_cut_state_eval es LPIVar = lp_cut_state_eval (LPCGoals (LPCAtom b#hs)#fs) LPIVar"
   using lpc_no_return_final_attachment[OF fixed_b, where r=r and rest="?pre" and
    extra="map Var extra" and pending=pending and payload=payload and saved=saved and caller_saved=es]
   by (elim exE) assumption
 show ?thesis using path initial final by auto
qed


theorem lpp_no_closed_call_traces_nonterminating:
 fixes A :: "(string lp_cut_symbol,string) term set"
 assumes initial: "a\<in>A" and distinct: "distinct vs"
   and cover: "\<forall>b\<in>A. vars_term b \<subseteq> set vs"
   and program: "lp_cut_source_program P"
   and closed: "\<And>b. b\<in>A \<Longrightarrow> \<exists>c\<in>A. \<exists>steps pending payload saved.
    lpp_no_return_trace fuel P reserved [(LPCGoals [LPCAtom b],map Var vs)] steps
      ((LPCGoals (LPCAtom c#pending),payload)#saved) \<and>
    lpp_no_return_boundaries [(LPCGoals [LPCAtom b],map Var vs)] steps \<and> steps\<noteq>[]"
 shows "\<not> SN_on
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
   {lp_cut_state_eval (LPCGoals (LPCAtom a#rest)#saved) LPIVar}"
proof (rule lp_source_call_recurrence[OF initial])
 fix b gs es assume member: "b\<in>A"
 obtain c steps pending payload saved where target: "c\<in>A"
   and checked: "lpp_no_return_trace fuel P reserved [(LPCGoals [LPCAtom b],map Var vs)] steps
      ((LPCGoals (LPCAtom c#pending),payload)#saved)"
   and boundaries: "lpp_no_return_boundaries [(LPCGoals [LPCAtom b],map Var vs)] steps"
   and nonempty: "steps\<noteq>[]"
   using closed[OF member] by auto
 have cover_b: "vars_term b \<subseteq> set vs" and cover_c: "vars_term c \<subseteq> set vs"
   using cover member target by auto
 have repeat: "\<exists>hs fs. (lp_cut_state_eval (LPCGoals (LPCAtom b#gs)#es) LPIVar,
   lp_cut_state_eval (LPCGoals (LPCAtom c#hs)#fs) LPIVar)
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   by (rule lpp_no_call_trace_repeat[OF checked boundaries nonempty distinct cover_b cover_c program])
 show "\<exists>c\<in>A. \<exists>hs fs. (lp_cut_state_eval (LPCGoals (LPCAtom b#gs)#es) LPIVar,
   lp_cut_state_eval (LPCGoals (LPCAtom c#hs)#fs) LPIVar)
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   using target repeat by auto
qed

ML \<open>
val checked = [@{thm lpp_no_call_trace_repeat}, @{thm lpp_no_closed_call_traces_nonterminating}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted checked call trace recurrence" else ();
\<close>
end
