theory LP_Cut_Domain_Return_Checker
  imports LP_Cut_Domain_Return_Certificate
begin

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem domain_return_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,(R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and ok: "check_lpc_return_constructor_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule precise_return_constructor_sound[OF domain tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_constructor_xml_def\<close>)
theorem domain_return_canonical_yes:
  assumes parsed: "parse_xml_string lpc_return_constructor_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and accepted: "check_lpc_return_constructor_xml xml"
  shows "logic_cut_terminates_in (\<lambda>t. D (cut_tree t)) P q modes"
proof (rule precise_canonical_termination)
  fix ts :: "(string logic_symbol,string) fo_term list"
  assume query: "logic_query (LogicUser q) modes (LogicUser q,ts)"
  have len: "length (map cut_term ts) = length modes"
    using query by (simp add: logic_query_def)
  have gr: "ground (map cut_term ts!i)" if "i\<in>set (lpc_positions modes)" for i
    using query that
    by (auto simp: logic_query_def lpc_positions_def list_all_iff set_zip cut_term_ground; blast)
  have native: "SN_on (precise_source (cut_program P))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) (map cut_term ts)))]]}"
    by (rule domain_return_xml_sound[OF parsed accepted len gr])
  show "SN_on (precise_source (cut_program P))
    {cut_state [LogicGoals [LogicAtom (LFun (LogicUser q) (map logic_embed ts))]]}"
    using native by (simp add: map_map o_def cut_tree_embed)
qed

end

theorem lp_cut_return_finite_yes:
  assumes parsed: "parse_xml_string lpc_return_constructor_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and accepted: "check_lpc_return_constructor_xml xml"
  shows "lp_cut_finite_terminates P q modes"
  using domain_return_canonical_yes[OF finite_cut.cut_runtime_domain_axioms parsed accepted]
  by (simp add: lp_cut_finite_terminates_def cut_finite_domain_iff)

theorem lp_cut_return_rational_yes:
  assumes parsed: "parse_xml_string lpc_return_constructor_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and accepted: "check_lpc_return_constructor_xml xml"
  shows "lp_cut_rational_terminates P q modes"
  using domain_return_canonical_yes[OF rational_cut.cut_runtime_domain_axioms parsed accepted]
  by (simp add: lp_cut_rational_terminates_def cut_rational_runtime_def)

corollary lp_cut_return_infinite_yes:
  assumes parsed: "parse_xml_string lpc_return_constructor_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and accepted: "check_lpc_return_constructor_xml xml"
  shows "lp_cut_infinite_terminates P q modes"
  using domain_return_canonical_yes[OF cut_unrestricted_runtime parsed accepted]
  by (simp add: lp_cut_infinite_terminates_def)

ML \<open>
  val results = @{thms lp_cut_return_finite_yes lp_cut_return_rational_yes lp_cut_return_infinite_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "Return category bridge: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("Return category bridge: unexpected oracles: " ^ commas unexpected)
  val _ = warning ("Cut return YES oracle dependencies: " ^ commas names)
\<close>
end
