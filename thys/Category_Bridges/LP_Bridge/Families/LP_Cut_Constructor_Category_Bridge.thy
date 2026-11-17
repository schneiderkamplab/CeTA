theory LP_Cut_Constructor_Category_Bridge
  imports Category_LP_Cut_Ranked_Bridge.LP_Cut_Ranked_Table_Checker
    Category_LP_Library.LP_Cut_Constructor_XML
begin

text \<open>The constructor certificate uses the same checked root table as
the basic table endpoint. Its constructor residual theorem supplies the child
termination premise; the domain interpretation is shared rather than repeated.\<close>

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem domain_constructor_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpc_constructor I J fuel P Q nds acts r q modes predicates constructors
      R outs fallback names marks filters q' n positions seed nfs prf"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule root_table_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ len ground])
  show "lpc_check_root_table fuel P Q nds acts r q modes"
    using ok by (simp add: check_lpc_constructor_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_constructor I J R outs fallback names marks filters q' n positions seed nfs prf"
    using ok by (auto simp: check_lpc_constructor_def Let_def)
  have "SN_on (lp_ild R) {[(q',map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule check_lp_constructor_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpc_constructor_def Let_def\<close>)
  then show "SN_on (lp_ild (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
    {[(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    using ok by (auto simp: check_lpc_constructor_def Let_def)
qed

theorem domain_constructor_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,(R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and ok: "check_lpc_constructor_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule domain_constructor_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_constructor_xml_def\<close>)
end

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem ranked_constructor_xml_yes:
  assumes parsed: "parse_xml_string lpc_constructor_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and accepted: "check_lpc_constructor_xml xml"
    and program: "cut_control_program P"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
  shows "logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t)))
    (cut_rank_program P) (q,length modes) modes"
proof (rule ranked_termination[OF _ projection])
  show "logic_cut_problem snd (cut_rank_program P) (q,length modes) modes"
    using program by (simp add: cut_rank_problem)
next
  fix ts :: "((string \<times> nat) logic_symbol,string) fo_term list"
  assume query: "logic_query (logic_symbol_arity snd) (LogicUser (q,length modes)) modes
    (LAtom (LogicUser (q,length modes)) ts)"
  have len: "length (map (cut_term \<circ> cut_unrank_term) ts) = length modes"
    using query by (simp add: logic_query_def)
  have grounds: "list_all (\<lambda>(t,b). b \<longrightarrow> logic_ground t) (zip ts modes)"
    using query unfolding logic_query_def by simp
  have gr: "ground (map (cut_term \<circ> cut_unrank_term) ts!i)"
    if "i\<in>set (lpc_positions modes)" for i
  proof -
    have i: "i < length modes" and mode: "modes!i" using that
      by (simp_all add: lpc_positions_def)
    have it: "i < length ts" using i len by simp
    have pair: "(ts!i,modes!i) \<in> set (zip ts modes)"
      using i it by (auto simp: in_set_zip)
    have "logic_ground (ts!i)"
      using list_all_iff[THEN iffD1, OF grounds] pair mode by auto
    then show ?thesis by (simp add: it cut_term_ground[symmetric])
  qed
  have native: "SN_on (source (cut_program P))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q)
      (map (\<lambda>t. lp_ieval t LPIVar) (map (cut_term \<circ> cut_unrank_term) ts)))]]}"
    by (rule domain_constructor_xml_sound[OF domain parsed accepted len gr])
  show "SN_on (source (cut_program P))
    {cut_erased_state [LogicGoals [LogicAtom (LAtom (q,length modes) (map logic_embed ts))]]}"
    using native by (simp add: map_map o_def cut_unrank_embed cut_tree_embed)
qed
end

text \<open>The guarded boundary checks ordinary heads and control arities.
Its acceptance is stronger than acceptance by the unchanged native checker.\<close>
definition check_lpc_ranked_constructor_xml :: "string \<Rightarrow> bool" where
  "check_lpc_ranked_constructor_xml xml \<longleftrightarrow> check_lpc_constructor_xml xml \<and>
    (case parse_xml_string lpc_constructor_parser xml of
      Left e \<Rightarrow> False |
      Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,child) \<Rightarrow>
        cut_program_shape P \<and> cut_control_program (cut_program_back P))"

lemma ranked_constructor_guarded_yes:
  assumes domain: "cut_runtime_domain D"
    and parsed: "parse_xml_string lpc_constructor_parser xml =
      Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,
        (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and checked: "check_lpc_ranked_constructor_xml xml"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
  shows "logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t)))
    (cut_rank_program (cut_program_back P)) (q,length modes) modes"
proof -
  have shape: "cut_program_shape P" and control: "cut_control_program (cut_program_back P)"
    and accepted: "check_lpc_constructor_xml xml"
    using checked parsed by (auto simp: check_lpc_ranked_constructor_xml_def)
  have inverse: "cut_program (cut_program_back P) = P"
    by (rule cut_program_forward_back[OF shape])
  show ?thesis by (rule ranked_constructor_xml_yes[OF domain _ accepted control projection])
    (simp only: inverse parsed)
qed
corollary lp_cut_constructor_finite_yes:
  assumes parsed: "parse_xml_string lpc_constructor_parser xml =
      Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,
        (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and checked: "check_lpc_ranked_constructor_xml xml"
  shows "lp_cut_finite_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
proof -
  have projection: "cut_finite_runtime (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      cut_finite_runtime (cut_tree (cut_unrank_tree
        (logic_arity_project (logic_symbol_arity snd) undefined u)))" for u
    by (simp add: cut_finite_domain_iff cut_finite_projection_closed)
  have domains: "(\<lambda>t. cut_finite_runtime (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) =
    (\<lambda>t. logic_finite t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto simp: cut_finite_domain_iff cut_typed_unrank_finite)
  show ?thesis using ranked_constructor_guarded_yes[OF finite_cut.cut_runtime_domain_axioms parsed checked projection]
    by (simp add: lp_cut_finite_terminates_def logic_cut_termination_domain_cong[OF domains])
qed

corollary lp_cut_constructor_rational_yes:
  assumes parsed: "parse_xml_string lpc_constructor_parser xml =
      Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,
        (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and checked: "check_lpc_ranked_constructor_xml xml"
  shows "lp_cut_rational_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
proof -
  have projection: "cut_rational_runtime (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      cut_rational_runtime (cut_tree (cut_unrank_tree
        (logic_arity_project (logic_symbol_arity snd) undefined u)))" for u
    by (simp add: cut_rational_runtime_def cut_rational_projection_closed)
  have domains: "(\<lambda>t. cut_rational_runtime (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) =
    (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto simp: cut_rational_runtime_def cut_typed_unrank_rational)
  show ?thesis using ranked_constructor_guarded_yes[OF rational_cut.cut_runtime_domain_axioms parsed checked projection]
    by (simp add: lp_cut_rational_terminates_def logic_cut_termination_domain_cong[OF domains])
qed

corollary lp_cut_constructor_infinite_yes:
  assumes parsed: "parse_xml_string lpc_constructor_parser xml =
      Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,
        (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and checked: "check_lpc_ranked_constructor_xml xml"
  shows "lp_cut_infinite_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
  using ranked_constructor_guarded_yes[OF cut_unrestricted_runtime parsed checked]
  by (simp add: lp_cut_infinite_terminates_def)


ML \<open>
  val results = @{thms lp_cut_constructor_finite_yes lp_cut_constructor_rational_yes lp_cut_constructor_infinite_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked constructor checker: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("Ranked constructor checker: unexpected oracles: " ^ commas unexpected)
\<close>
end
