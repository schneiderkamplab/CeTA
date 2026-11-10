theory LP_Cut_Domain_Return_Module_Triples
  imports LP_Cut_Domain_Return_Module_Certificate Category_LP_Library.LP_Cut_Return_Module_Triples_XML
begin

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)
theorem precise_return_module_triples_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpc_return_module_triples I J fuel P Q nds states returned arity acts r q modes predicates constructors
      triples R outs fallback dnames pnames marks filters q' n positions labs proofs"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule precise_return_module_root_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ len ground])
  show "lpc_return_module_check_root fuel P Q nds states returned arity acts r q modes"
    using ok by (simp add: check_lpc_return_module_triples_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_initial_triples I J triples R outs fallback dnames pnames marks filters q' n positions labs proofs"
    using ok by (auto simp: check_lpc_return_module_triples_def Let_def)
  have "SN_on (lp_ild R) {[(q',map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule check_lp_initial_triples_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpc_return_module_triples_def Let_def\<close>)
  then show "SN_on (lp_ild (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
    {[(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    using ok by (auto simp: check_lpc_return_module_triples_def Let_def)
qed



theorem domain_return_module_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_module_triples_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,(triples,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpc_return_module_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule precise_return_module_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_module_triples_xml_def\<close>)
theorem domain_return_module_triples_canonical_yes:
  assumes parsed: "parse_xml_string lpc_return_module_triples_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (triples,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and accepted: "check_lpc_return_module_triples_xml xml"
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
    by (rule domain_return_module_triples_xml_sound[OF parsed accepted len gr])
  show "SN_on (precise_source (cut_program P))
    {cut_state [LogicGoals [LogicAtom (LFun (LogicUser q) (map logic_embed ts))]]}"
    using native by (simp add: map_map o_def cut_tree_embed)
qed

end

theorem lp_cut_return_module_triples_finite_yes:
  assumes parsed: "parse_xml_string lpc_return_module_triples_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (triples,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and accepted: "check_lpc_return_module_triples_xml xml"
  shows "lp_cut_finite_terminates P q modes"
  using domain_return_module_triples_canonical_yes[OF finite_cut.cut_runtime_domain_axioms parsed accepted]
  by (simp add: lp_cut_finite_terminates_def cut_finite_domain_iff)

theorem lp_cut_return_module_triples_rational_yes:
  assumes parsed: "parse_xml_string lpc_return_module_triples_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (triples,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and accepted: "check_lpc_return_module_triples_xml xml"
  shows "lp_cut_rational_terminates P q modes"
  using domain_return_module_triples_canonical_yes[OF rational_cut.cut_runtime_domain_axioms parsed accepted]
  by (simp add: lp_cut_rational_terminates_def cut_rational_runtime_def)

corollary lp_cut_return_module_triples_infinite_yes:
  assumes parsed: "parse_xml_string lpc_return_module_triples_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (triples,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and accepted: "check_lpc_return_module_triples_xml xml"
  shows "lp_cut_infinite_terminates P q modes"
  using domain_return_module_triples_canonical_yes[OF cut_unrestricted_runtime parsed accepted]
  by (simp add: lp_cut_infinite_terminates_def)

ML \<open>
  val results = @{thms lp_cut_return_module_triples_finite_yes lp_cut_return_module_triples_rational_yes lp_cut_return_module_triples_infinite_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "Return module triple category bridge: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("Return module triple category bridge: unexpected oracles: " ^ commas unexpected)
  val _ = warning ("Cut return module triple YES oracle dependencies: " ^ commas names)
\<close>
end
