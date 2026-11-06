theory LP_Prolog_Helper_Call_Query
  imports LP_Prolog_Helper_Call_LTS
begin

lemma lpp_helper_lts_query_nontermination:
  assumes rules: "transition_rules system=set (map (lpp_helper_edge_transition views) call_edges)"
    and checked: "list_all (lpp_helper_edge_shape P interfaces views) call_edges"
    and entry: "\<And>loc. loc\<in>lts.initial system \<Longrightarrow>
      fst (views loc)=q \<and> length (snd (views loc))=length modes \<and>
      list_all (\<lambda>i. i<length modes) (interfaces (q,length modes))"
    and child: "\<not>LPPIntegerLTS.lts_termination system"
  shows "\<exists>argv. length argv=length modes \<and> list_all ground argv \<and>
    \<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  obtain s where start: "s\<in>LPPIntegerLTS.initial_states system"
    and no: "\<not>SN_on (lpp_helper_call_relation P interfaces
      (map (lpp_call_edge_recipe views) call_edges)) {lpp_call_state views s}"
    using lpp_helper_lts_initial_nontermination[OF rules checked child] by blast
  have entry_view: "fst (views (LTS.location s))=q"
    and entry_length: "length (snd (views (LTS.location s)))=length modes"
    and bounds: "list_all (\<lambda>i. i<length modes) (interfaces (q,length modes))"
    using start entry by (auto simp: LPPIntegerLTS.initial_states_def)
  let ?ns = "map (lpp_recurrence_state_values s) (snd (views (LTS.location s)))"
  have represented: "lpp_partial_call_represents interfaces (lpp_call_state views s)
      [LPCGoals [LPCAtom (LPIFun (LPCUser q) (map lpp_integer_value ?ns))]]"
    using bounds by (auto simp: lpp_partial_call_represents_def lpp_call_state_def
      entry_view entry_length lpp_partial_observations_def list_all_iff)
  have source_no: "\<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map lpp_integer_value ?ns))]]}"
    by (rule lpp_helper_call_relation_source_no[OF no represented])
  let ?argv = "map lpp_integer_term ?ns"
  have argv_length: "length ?argv=length modes" using entry_length by simp
  have argv_ground: "list_all ground ?argv"
    by (simp add: list_all_iff lpp_integer_term_def ground_vars_term_empty)
  have argv_eval: "map (\<lambda>t. lp_ieval t LPIVar) ?argv=map lpp_integer_value ?ns"
    by (simp add: map_map o_def)
  show ?thesis by (rule exI[of _ "?argv"])
    (use argv_length argv_ground source_no in \<open>simp only: argv_eval; blast\<close>)
qed

ML \<open>
val checked = [@{thm lpp_helper_lts_query_nontermination}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper call query dependency" else ();
\<close>
end
