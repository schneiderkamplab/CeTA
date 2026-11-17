theory LP_Prolog_Finite_Local_Composition
 imports LP_Prolog_Finite_Local_Region
begin

text \<open>Close the referenced module graph only when every represented module
supplies its complete termination and actual-return contract. Residual descent
does not establish the local contracts or initialize contexts.\<close>

theorem lpp_finite_local_graph_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes sn: "SN_on R {a}"
    and represented: "lpp_stable_triple_root_rep operation SP contexts roots ss a ret"
    and finite: "lpp_finite_direct_invariant A ss"
    and modules: "\<And>i eta. i<length roots \<Longrightarrow> i<length contexts \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i))))
        (lpcn_guards (lpctr_node (roots!i))) eta \<Longrightarrow>
      lpc_free_knowledge (set (lpctr_free (roots!i))) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state (roots!i))) \<Longrightarrow>
      (\<And>vs b final. (lp_atom_eval (lpctr_input (roots!i)) eta,b)\<in>R \<Longrightarrow>
        lpp_stable_triple_root_rep operation SP contexts roots vs b final \<Longrightarrow>
        lpp_finite_direct_invariant A vs \<Longrightarrow>
        lpp_stable_triple_answer_contract operation P vs Q final) \<Longrightarrow>
      lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state (roots!i))) Q
        (lp_atom_eval (lpctr_output (roots!i)))"
  shows "lpp_stable_triple_answer_contract operation P ss Q ret"
proof (rule lpp_stable_triple_answer_contract_modular[where
    rep="\<lambda>us b out. lpp_stable_triple_root_rep operation SP contexts roots us b out \<and> lpp_finite_direct_invariant A us", OF sn conjI[OF represented finite]])
  fix us b out
  assume rep: "lpp_stable_triple_root_rep operation SP contexts roots us b out \<and> lpp_finite_direct_invariant A us"
    and lower: "\<And>vs c final. (b,c)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots vs c final \<and> lpp_finite_direct_invariant A vs \<Longrightarrow>
      lpp_stable_triple_answer_contract operation P vs Q final"
  obtain i eta where index: "i<length roots" "i<length contexts"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i))))
      (lpcn_guards (lpctr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (lpctr_free (roots!i))) eta"
    and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
    and source: "us=lpc_return_eval eta (lpc_triple_root_state (roots!i))"
    and call: "b=lp_atom_eval (lpctr_input (roots!i)) eta"
    and output_atom: "out=lp_atom_eval (lpctr_output (roots!i))"
    using rep by (auto simp: lpp_stable_triple_root_rep_def)
  show "lpp_stable_triple_answer_contract operation P us Q out"
    unfolding source output_atom
    by (rule modules[OF index known free observed])
      (use rep lower in \<open>auto simp only: source call\<close>)
qed

ML \<open>
val checked = [@{thm lpp_finite_local_graph_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable guarded composition dependency" else ();
\<close>
end
