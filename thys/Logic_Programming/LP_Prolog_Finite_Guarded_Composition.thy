theory LP_Prolog_Finite_Guarded_Composition
 imports LP_Prolog_Finite_Guarded_XML
   LP_Prolog_Finite_Relational_Return LP_Prolog_Finite_Numeric_Projection
   LP_Prolog_Finite_Guarded_Descent
begin

text \<open>These interfaces retain the established finite source regions and
Split contracts while allowing their descent obligations to use a guarded
relation. A numeric child discharges only that relation. Actual successful
helper returns, complete dependency coverage and the source entry remain
checked obligations. The guarded graph and XML checker bind them to the
projected numeric child; native assembly and export are separate integration
steps.\<close>


text \<open>Close the finite referenced module graph using one checked descent
relation. Every represented module must supply its local contract under exactly
the contracts of its outgoing dependencies. This includes helper and continuation
modules; termination of a numeric child alone supplies none of those contracts.\<close>

theorem lpp_finite_guarded_graph_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes sn: "SN_on R {a}"
    and represented: "lpp_finite_triple_root_rep SP contexts roots ss a ret"
    and modules: "\<And>i eta. i<length roots \<Longrightarrow> i<length contexts \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i))))
        (lpcn_guards (lpctr_node (roots!i))) eta \<Longrightarrow>
      lpc_free_knowledge (set (lpctr_free (roots!i))) eta \<Longrightarrow>
      lpp_evaluation_context_holds lpp_finite_evaluation_result SP (contexts!i) eta \<Longrightarrow>
      (\<And>vs b final. (lp_atom_eval (lpctr_input (roots!i)) eta,b)\<in>R \<Longrightarrow>
        lpp_finite_triple_root_rep SP contexts roots vs b final \<Longrightarrow>
        lpp_finite_triple_answer_contract P vs Q final) \<Longrightarrow>
      lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state (roots!i))) Q
        (lp_atom_eval (lpctr_output (roots!i)))"
  shows "lpp_finite_triple_answer_contract P ss Q ret"
proof (rule lpp_finite_triple_answer_contract_modular[where
    rep="lpp_finite_triple_root_rep SP contexts roots", OF sn represented])
  fix us b out
  assume rep: "lpp_finite_triple_root_rep SP contexts roots us b out"
    and lower: "\<And>vs c final. (b,c)\<in>R \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots vs c final \<Longrightarrow>
      lpp_finite_triple_answer_contract P vs Q final"
  obtain i eta where index: "i<length roots" "i<length contexts"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i))))
      (lpcn_guards (lpctr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (lpctr_free (roots!i))) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (contexts!i) eta"
    and source: "us=lpc_return_eval eta (lpc_triple_root_state (roots!i))"
    and call: "b=lp_atom_eval (lpctr_input (roots!i)) eta"
    and output_atom: "out=lp_atom_eval (lpctr_output (roots!i))"
    using rep by (auto simp: lpp_finite_triple_root_rep_def)
  show "lpp_finite_triple_answer_contract P us Q out"
    unfolding source output_atom
    by (rule modules[OF index known free observed])
      (use lower in \<open>auto simp only: call\<close>)
qed

ML \<open>
val checked = [@{thm check_lpp_established_finite_guarded_xml_sound},
  @{thm lpp_check_finite_guarded_numeric_graph_sound},
  @{thm lpp_finite_guarded_graph_root_sound},
  @{thm lpp_finite_guarded_component_checked_lower},
  @{thm lpp_finite_guarded_split_first_descent},
  @{thm lpp_finite_guarded_split_return_descent},
  @{thm lpp_finite_guarded_region_descent_checked},
  @{thm lpp_finite_actual_return_observed_descent},
  @{thm lpp_finite_guarded_integer_split_checked_lower},
  @{thm lpp_finite_guarded_ground_split_checked_lower},
  @{thm lpp_finite_guarded_shape_split_checked_lower},
  @{thm lpp_finite_context_connection_descent},
  @{thm lpp_check_finite_projected_numeric_component_sound},
  @{thm lpp_finite_projected_calls_SN},
  @{thm lpp_finite_guarded_graph_contract},
  @{thm lpp_finite_guarded_connection_checked_lower},
  @{thm lpp_finite_guarded_region_contexts_checked_lower},
  @{thm lpp_finite_guarded_split_interface_lower},
  @{thm lpp_finite_relational_return_context},
  @{thm lpp_check_finite_numeric_component_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite guarded composition dependency" else ();
\<close>
end
