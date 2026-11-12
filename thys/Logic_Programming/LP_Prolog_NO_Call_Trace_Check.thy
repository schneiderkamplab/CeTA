theory LP_Prolog_NO_Call_Trace_Check
 imports LP_Prolog_NO_Call_Trace_Recurrence
begin

definition lpp_no_call_trace_edge where
 "lpp_no_call_trace_edge fuel P reserved vs calls a steps =
   (steps\<noteq>[] \<and> (case snd (last steps) of
    (LPCGoals (LPCAtom b#pending),payload)#saved \<Rightarrow>
      b\<in>set calls \<and>
      lpp_no_return_trace fuel P reserved [(LPCGoals [LPCAtom a],map Var vs)] steps
        ((LPCGoals (LPCAtom b#pending),payload)#saved) \<and>
      lpp_no_return_boundaries [(LPCGoals [LPCAtom a],map Var vs)] steps
    | _ \<Rightarrow> False))"

definition lpp_no_call_trace_check where
 "lpp_no_call_trace_check fuel P reserved vs calls edges a =
   (lp_cut_source_program P \<and> distinct vs \<and> a\<in>set calls \<and>
    list_all (\<lambda>b. vars_term b \<subseteq> set vs) calls \<and>
    list_all (\<lambda>b. list_ex (\<lambda>(c,steps). c=b \<and>
      lpp_no_call_trace_edge fuel P reserved vs calls b steps) edges) calls)"

lemma lpp_no_call_trace_edge_sound:
 assumes checked: "lpp_no_call_trace_edge fuel P reserved vs calls a steps"
 shows "\<exists>b\<in>set calls. \<exists>pending payload saved.
    lpp_no_return_trace fuel P reserved [(LPCGoals [LPCAtom a],map Var vs)] steps
      ((LPCGoals (LPCAtom b#pending),payload)#saved) \<and>
    lpp_no_return_boundaries [(LPCGoals [LPCAtom a],map Var vs)] steps \<and> steps\<noteq>[]"
proof -
 obtain row saved where rows: "snd (last steps)=row#saved"
   using checked by (cases "snd (last steps)") (auto simp: lpp_no_call_trace_edge_def)
 obtain e payload where row: "row=(e,payload)" by (cases row) auto
 obtain gs where goals: "e=LPCGoals gs"
   using checked by (cases e) (auto simp: lpp_no_call_trace_edge_def rows row)
 obtain g pending where cons: "gs=g#pending"
   using checked by (cases gs) (auto simp: lpp_no_call_trace_edge_def rows row goals)
 obtain b where atom: "g=LPCAtom b"
   using checked by (cases g) (auto simp: lpp_no_call_trace_edge_def rows row goals cons)
 show ?thesis using checked
   by (auto simp: lpp_no_call_trace_edge_def rows row goals cons atom)
qed

theorem lpp_no_call_trace_check_sound:
 assumes checked: "lpp_no_call_trace_check fuel P reserved vs calls edges a"
 shows "\<not> SN_on
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
   {lp_cut_state_eval (LPCGoals (LPCAtom a#rest)#saved) LPIVar}"
proof -
 have initial: "a\<in>set calls" and distinct: "distinct vs"
   and cover: "\<forall>b\<in>set calls. vars_term b \<subseteq> set vs"
   and program: "lp_cut_source_program P"
   and edges: "\<forall>b\<in>set calls. \<exists>c steps. (c,steps)\<in>set edges \<and> c=b \<and>
      lpp_no_call_trace_edge fuel P reserved vs calls b steps"
   using checked by (auto simp: lpp_no_call_trace_check_def list_all_iff list_ex_iff)
 show ?thesis
 proof (rule lpp_no_closed_call_traces_nonterminating[OF initial distinct cover program])
  fix b assume "b\<in>set calls"
  then obtain steps where edge: "lpp_no_call_trace_edge fuel P reserved vs calls b steps"
    using edges by auto
  show "\<exists>c\<in>set calls. \<exists>steps pending payload saved.
    lpp_no_return_trace fuel P reserved [(LPCGoals [LPCAtom b],map Var vs)] steps
      ((LPCGoals (LPCAtom c#pending),payload)#saved) \<and>
    lpp_no_return_boundaries [(LPCGoals [LPCAtom b],map Var vs)] steps \<and> steps\<noteq>[]"
    using lpp_no_call_trace_edge_sound[OF edge] by blast
 qed
qed

ML \<open>
val checked = [@{thm lpp_no_call_trace_check_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite call trace checker" else ();
\<close>
end
