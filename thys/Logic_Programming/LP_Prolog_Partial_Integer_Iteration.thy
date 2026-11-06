theory LP_Prolog_Partial_Integer_Iteration
  imports LP_Prolog_Partial_Integer_Selection
begin

text \<open>The recursive call may have arbitrary outputs and an arbitrary later_goals.
The later_goals remains pending; no property of its eventual success is assumed.\<close>

lemma lpp_partial_selected_source_iteration:
  assumes selection: "lp_cut_slice P (LPCUser f) (length H)=earlier@c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var H),
      map lpp_recurrence_goal ops @ LPCAtom tail#later_goals)"
    and ordinary: "(f,length H)\<notin>lpp_builtin_signature"
    and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
      (LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    and observed_head: "\<And>x. x\<in>set K \<Longrightarrow> x\<in>set H"
    and observed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
    and checked: "lpp_partial_recurrence_check H K ops"
    and guards: "lpp_recurrence_guards ops rho"
  shows "\<exists>m. (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending)#es,
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t
        (lpp_partial_environment H (lpp_recurrence_known K ops)
          (lpp_recurrence_values ops rho) eta))) (LPCAtom tail#later_goals) @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#
      (map (\<lambda>d. LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d m) cs @ LPCBarrier m#es))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?a = "lp_ieval (Fun (LPCUser f) (map Var H)) eta"
  let ?bs = "map lpp_recurrence_goal ops @ LPCAtom tail#later_goals"
  let ?initial = "lpp_partial_environment H K rho eta"
  let ?final = "lpp_partial_environment H (lpp_recurrence_known K ops)
      (lpp_recurrence_values ops rho) eta"
  let ?pending = "map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending"
  have initial: "lpc_fresh_head_environment H eta=?initial"
    by (rule lpp_partial_initial_environment[OF observed_head observed])
  obtain m where prefix: "(LPCGoals (LPCAtom ?a#pending)#es,
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t ?initial)) ?bs @ ?pending)#
      (map (\<lambda>d. LPCClause (LPCAtom ?a#pending) d m) cs @ LPCBarrier m#es))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_partial_selected_clause_steps[OF selection index clause ordinary failed]
    by (simp only: initial; blast)
  let ?saved = "map (\<lambda>d. LPCClause (LPCAtom ?a#pending) d m) cs @ LPCBarrier m#es"
  note body = lpp_partial_body_source_steps[OF checked guards,
    where rest="map (lp_cut_bind m id) (LPCAtom tail#later_goals)" and es="?saved"
      and P=P and eta=eta and pending=pending]
  have steps: "(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t ?initial)) ?bs @ ?pending)#?saved,
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t ?final)) (LPCAtom tail#later_goals) @ ?pending)#?saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    using body by (simp add: map_map lp_cut_map_bind lpp_recurrence_bind_goal o_def)
  show ?thesis using trancl_rtrancl_trancl[OF prefix steps] by blast
qed

ML \<open>
val checked = [@{thm lpp_partial_selected_source_iteration}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial source iteration dependency" else ();
\<close>
end
