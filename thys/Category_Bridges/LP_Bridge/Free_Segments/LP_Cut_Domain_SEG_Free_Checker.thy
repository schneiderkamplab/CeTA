theory LP_Cut_Domain_SEG_Free_Checker
  imports LP_Cut_Domain_SEG_Free_Certificate
begin

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem domain_seg_free_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_seg_free_certificate_parser xml =
    Right (P,q,modes,fuel,roots,Fs,regions,continuations,controls,data_map,fallback,constructors,trs_rules,prf)"
    and ok: "check_lpc_seg_free_certificate_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  have values_ground: "\<forall>(t,b)\<in>set (zip (map (\<lambda>t. lp_ieval t LPIVar) ts) modes).
      b \<longrightarrow> lp_seg_ground t"
    using len ground by (auto simp: in_set_zip lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  have values_domain: "list_all D (map (\<lambda>t. lp_ieval t LPIVar) ts)"
    by (auto simp: list_all_iff intro: valuation_domain variables)
  show ?thesis
    by (rule precise_check_lpc_seg_free_certificate_sound[OF _ _ _ _ values_ground values_domain])
      (use domain tp_rbt_impl dpp_rbt_impl parsed ok len in \<open>auto simp: check_lpc_seg_free_certificate_xml_def\<close>)
qed
theorem domain_seg_free_canonical_yes:
  assumes parsed: "parse_xml_string lpc_seg_free_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,roots,Fs,regions,continuations,controls,data_map,fallback,constructors,trs_rules,prf)"
    and accepted: "check_lpc_seg_free_certificate_xml xml"
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
    by (rule domain_seg_free_xml_sound[OF parsed accepted len gr])
  show "SN_on (precise_source (cut_program P))
    {cut_state [LogicGoals [LogicAtom (LFun (LogicUser q) (map logic_embed ts))]]}"
    using native by (simp add: map_map o_def cut_tree_embed)
qed

end

theorem lp_cut_seg_free_finite_yes:
  assumes parsed: "parse_xml_string lpc_seg_free_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,roots,Fs,regions,continuations,controls,data_map,fallback,constructors,trs_rules,prf)"
    and accepted: "check_lpc_seg_free_certificate_xml xml"
  shows "lp_cut_finite_terminates P q modes"
  using domain_seg_free_canonical_yes[OF finite_cut.cut_runtime_domain_axioms parsed accepted]
  by (simp add: lp_cut_finite_terminates_def cut_finite_domain_iff)

theorem lp_cut_seg_free_rational_yes:
  assumes parsed: "parse_xml_string lpc_seg_free_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,roots,Fs,regions,continuations,controls,data_map,fallback,constructors,trs_rules,prf)"
    and accepted: "check_lpc_seg_free_certificate_xml xml"
  shows "lp_cut_rational_terminates P q modes"
  using domain_seg_free_canonical_yes[OF rational_cut.cut_runtime_domain_axioms parsed accepted]
  by (simp add: lp_cut_rational_terminates_def cut_rational_runtime_def)

corollary lp_cut_seg_free_infinite_yes:
  assumes parsed: "parse_xml_string lpc_seg_free_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,roots,Fs,regions,continuations,controls,data_map,fallback,constructors,trs_rules,prf)"
    and accepted: "check_lpc_seg_free_certificate_xml xml"
  shows "lp_cut_infinite_terminates P q modes"
  using domain_seg_free_canonical_yes[OF cut_unrestricted_runtime parsed accepted]
  by (simp add: lp_cut_infinite_terminates_def)

ML \<open>
  val results = @{thms lp_cut_seg_free_finite_yes lp_cut_seg_free_rational_yes lp_cut_seg_free_infinite_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "SEG_Free category bridge: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("SEG_Free category bridge: unexpected oracles: " ^ commas unexpected)
  val _ = warning ("Cut free seg YES oracle dependencies: " ^ commas names)
\<close>
end
