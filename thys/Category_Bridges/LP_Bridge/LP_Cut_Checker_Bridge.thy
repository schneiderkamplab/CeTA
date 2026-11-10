theory LP_Cut_Checker_Bridge
  imports LP_Cut_Representation Category_LP_Library.LP_Cut_Table_XML
begin

text \<open>This concrete serialized corollary is for the separately named
infinite-tree variant. Its premises bind the exact source and query to actual
assumption-free checker acceptance. It does not relabel that verdict as a
finite-term or rational-tree result.\<close>
theorem lp_cut_table_infinite_yes:
  assumes parsed: "parse_xml_string lpc_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,filters,(q',n,positions),prf))"
    and accepted: "check_lpc_xml xml"
  shows "lp_cut_infinite_terminates P q modes"
proof (rule cut_native_termination)
  fix ts :: "(string logic_symbol,string) fo_term list"
  assume query: "logic_query (LogicUser q) modes (LogicUser q,ts)"
  have len: "length (map cut_term ts) = length modes"
    using query by (simp add: logic_query_def)
  have gr: "ground (map cut_term ts!i)" if "i\<in>set (lpc_positions modes)" for i
    using query that
    by (auto simp: logic_query_def lpc_positions_def list_all_iff set_zip cut_term_ground; blast)
  have native: "SN_on (lp_cut_source (cut_program P))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) (map cut_term ts)))]]}"
    by (rule check_lpc_xml_sound[OF parsed accepted len gr])
  show "SN_on (lp_cut_source (cut_program P))
    {cut_state [LogicGoals [LogicAtom (LFun (LogicUser q) (map logic_embed ts))]]}"
    using native by (simp add: map_map o_def cut_tree_embed)
qed

ML \<open>
  val results = @{thms cut_tree_roundtrip cut_tree_native_roundtrip
    cut_tree_subst cut_tree_eval cut_admin cut_slice cut_lower
    cut_unifiable_iff cut_equalizable_iff cut_infinite_step_native
    cut_native_termination lp_cut_table_infinite_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "LP cut: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("LP cut: unexpected oracle dependencies: " ^ commas unexpected)
  val _ = warning ("LP cut category oracle dependencies: " ^ commas names)
\<close>
end
