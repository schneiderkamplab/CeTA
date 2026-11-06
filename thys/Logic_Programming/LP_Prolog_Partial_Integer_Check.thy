theory LP_Prolog_Partial_Integer_Check
  imports LP_Prolog_Partial_Integer_Query LP_Prolog_Integer_Call_Check
begin

definition lpp_partial_interfaces where
  "lpp_partial_interfaces masks signature = (case map_of masks signature of
    None \<Rightarrow> [] | Some positions \<Rightarrow> positions)"

definition lpp_check_partial_integer_calls where
  "lpp_check_partial_integer_calls P q modes masks bindings call_edges child prf =
    (distinct (map fst masks) \<and>
     list_all (\<lambda>((predicate,arity),positions). list_all (\<lambda>i. i<arity) positions) masks \<and>
     distinct (map fst bindings) \<and>
     list_all (\<lambda>(loc,predicate,coordinates). distinct coordinates) bindings \<and>
     list_all (\<lambda>(from_loc,to_loc,recipe).
       from_loc\<in>set (map fst bindings) \<and> to_loc\<in>set (map fst bindings)) call_edges \<and>
     list_all (lpp_partial_edge_shape P (lpp_partial_interfaces masks) (lpp_call_views bindings)) call_edges \<and>
     list_all (\<lambda>loc. loc\<in>set (map fst bindings) \<and>
       fst (lpp_call_views bindings loc)=q \<and>
       length (snd (lpp_call_views bindings loc))=length modes \<and>
       list_all (\<lambda>i. i<length modes) (lpp_partial_interfaces masks (q,length modes))) (lts_impl.initial child) \<and>
     map snd (transitions_impl child)=map (lpp_call_edge_transition (lpp_call_views bindings)) call_edges \<and>
     isOK (check_its4 child False prf))"

theorem lpp_check_partial_integer_calls_sound:
  assumes checked: "lpp_check_partial_integer_calls P q modes masks bindings call_edges child prf"
  shows "\<exists>argv. length argv=length modes \<and> list_all ground argv \<and>
    \<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have exact_rules: "map snd (transitions_impl child)=
      map (lpp_call_edge_transition (lpp_call_views bindings)) call_edges"
    using checked unfolding lpp_check_partial_integer_calls_def by blast
  have rules: "transition_rules (lts_of child)=
      set (map (lpp_call_edge_transition (lpp_call_views bindings)) call_edges)"
    by (simp only: lts_of_simps set_map[symmetric] exact_rules)
  have shapes: "list_all (lpp_partial_edge_shape P (lpp_partial_interfaces masks) (lpp_call_views bindings)) call_edges"
    using checked unfolding lpp_check_partial_integer_calls_def by blast
  have entry: "fst (lpp_call_views bindings loc)=q \<and>
      length (snd (lpp_call_views bindings loc))=length modes \<and>
      list_all (\<lambda>i. i<length modes) (lpp_partial_interfaces masks (q,length modes))"
    if "loc\<in>lts.initial (lts_of child)" for loc
    using checked that unfolding lpp_check_partial_integer_calls_def
    by (simp only: lts_of_simps list_all_iff; blast)
  have child_no: "\<not>LPPIntegerLTS.lts_termination (lts_of child)"
    using check_its4_sound[of child False "prf"] checked
    by (simp add: lpp_check_partial_integer_calls_def)
  show ?thesis by (rule lpp_partial_lts_query_nontermination[OF rules shapes entry child_no])
qed

ML \<open>
val checked = [@{thm lpp_check_partial_integer_calls_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_its4_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted arithmetic call checker dependency" else ();
\<close>
end
