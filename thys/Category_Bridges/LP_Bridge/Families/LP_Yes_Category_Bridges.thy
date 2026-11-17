theory LP_Yes_Category_Bridges
  imports Category_LP_Bridge.LP_Ranked_Checker_Bridge
    Category_LP_Library.LP_Constructor_XML Category_LP_Library.LP_Dependency_Triple_XML
begin

text \<open>The pure-LP YES endpoints all prove the same conservative source
property. This common query translation binds their parsed source and ground
positions to each canonical runtime domain. The finite-named endpoint is connected through its actual check definition: it
uses the same check whose stronger TOCL09 theorem covers arbitrary runtime trees.\<close>

lemma logic_checked_query_transfer:
  fixes P :: "((string,nat list) lab,string) logic_clause list"
  assumes modes: "set positions = {i. i<length modes \<and> modes!i}"
    and native: "\<And>ts :: (((string,nat list) lab),string) term list.
      length ts=length modes \<Longrightarrow>
      (\<And>i. i\<in>set positions \<Longrightarrow> ground (ts!i)) \<Longrightarrow>
      SN_on (lp_ild (logic_to_program P)) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
proof -
  have all: "logic_terminates_in snd D (logic_rank_program P) (q,length modes) modes" for D
  proof (rule logic_ranked_native_termination)
    fix a :: "((string,nat list) lab \<times> nat,((string,nat list) lab \<times> nat,string) fo_term) logic_atom"
    assume query: "logic_query snd (q,length modes) modes a"
    let ?ts = "map (to_term \<circ> logic_unrank_term) (logic_arguments a)"
    have len: "length ?ts=length modes" using query by (cases a) (simp add: logic_query_def)
    have gr: "ground (?ts!i)" if pos: "i\<in>set positions" and i: "i<length modes" for i
    proof -
      have length: "length (logic_arguments a)=length modes" using len by simp
      have mode: "modes!i" using modes pos by auto
      have constraint: "list_all (\<lambda>(t,b). b \<longrightarrow> logic_ground t)
        (zip (logic_arguments a) modes)" using query unfolding logic_query_def by blast
      have member: "(logic_arguments a!i,modes!i)\<in>set (zip (logic_arguments a) modes)"
        using i length by (auto simp: set_zip)
      have ground: "logic_ground (logic_arguments a!i)"
        using constraint member mode by (auto simp: list_all_iff)
      show ?thesis using ground i length
        by (simp add: logic_ground_translation[symmetric])
    qed
    have sn: "SN_on (lp_ild (logic_to_program P)) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ?ts)]}"
      by (rule native[OF len]) (use gr modes in auto)
    show "SN_on (lp_ild (logic_to_program P))
      {logic_to_goals [logic_atom_map logic_embed (logic_erase_atom logic_unrank_term a)]}"
      using sn query by (cases a)
        (simp add: logic_to_goals_def logic_query_def map_map o_def logic_embed_translation)
  qed
  show ?thesis using all
    unfolding lp_finite_terminates_def lp_rational_terminates_def lp_infinite_terminates_def by blast
qed

theorem lp_constructor_category_yes:
  assumes parsed: "parse_xml_string lp_constructor_parser xml =
    Right (logic_to_program P,outs,fallback,names,marks,filters,(q,length modes,positions),seed,nfs,prf)"
    and accepted: "check_lp_constructor_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
  by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_constructor_xml_sound[OF parsed accepted]) auto

theorem lp_residual_constructor_category_yes:
  assumes parsed: "parse_xml_string lp_residual_constructor_parser xml =
    Right (logic_to_program P,(q,length modes,positions),fuel,root_id,nds,
      (Q,outs,fallback,names,marks,filters,(q',n',positions'),seed,nfs,prf))"
    and accepted: "check_lp_residual_constructor_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
  by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_residual_constructor_xml_sound[OF parsed accepted]) auto

theorem lp_pidp_category_yes:
  assumes parsed: "parse_xml_string lp_pidp_parser xml =
    Right (logic_to_program P,outs,fallback,names,marks,filters,(q,length modes,positions),labs,proofs)"
    and accepted: "check_lp_pidp_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
  by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_pidp_xml_sound[OF parsed accepted]) auto

theorem lp_pidp_mode_category_yes:
  assumes parsed: "parse_xml_string lp_pidp_mode_parser xml =
    Right (logic_to_program P,(q,length modes,positions),aliases,(Q,outs,fallback,names,marks,filters,(q',n_child,g1),labs,proofs))"
    and accepted: "check_lp_pidp_mode_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
  by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_pidp_mode_xml_sound[OF parsed accepted]) auto

theorem lp_simplify_category_yes:
  assumes parsed: "parse_xml_string lp_simplify_parser xml =
    Right (logic_to_program P,(q,length modes,positions),(Q,(q1,n1,g1),aliases,
      (T,outs,fallback,names,marks,filters,(q2,n2,g2),labs,proofs)))"
    and accepted: "check_lp_simplify_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
  by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_simplify_xml_sound[OF parsed accepted]) auto

theorem lp_residual_category_yes:
  assumes parsed: "parse_xml_string lp_residual_parser xml =
    Right (logic_to_program P,(q,length modes,positions),fuel,root_id,nds,
      (Q,outs,fallback,names,filters,(q',n',positions'),prf))"
    and accepted: "check_lp_residual_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
  by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_residual_xml_sound[OF parsed accepted]) auto

theorem lp_source_graph_category_yes:
  assumes parsed: "parse_xml_string lp_source_graph_parser xml = Right (logic_to_program P,(q,length modes,positions),fuel,root_id,nds)"
    and accepted: "check_lp_source_graph_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
  by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_source_graph_xml_sound[OF parsed accepted]) simp

theorem lp_seg_category_yes:
  assumes parsed: "parse_xml_string lp_seg_parser xml = Right (logic_to_program P,(q,length modes,positions),fuel,root_id,nds,trs_rules,prf)"
    and accepted: "check_lp_seg_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
proof (rule logic_checked_query_transfer[OF modes])
  fix ts :: "((string,nat list) lab,string) term list"
  assume len: "length ts=length modes" and gr: "\<And>i. i\<in>set positions \<Longrightarrow> ground (ts!i)"
  show "SN_on (lp_ild (logic_to_program P)) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
    by (rule check_lp_seg_xml_sound[OF parsed accepted])
      (use len gr modes in \<open>auto simp: lp_seg_ground_eval ground_vars_term_empty\<close>)
qed

theorem lp_initial_triples_category_yes:
  assumes parsed: "parse_xml_string lp_initial_triples_parser xml =
      Right (D,logic_to_program P,outs,fallback,dnames,pnames,marks,filters,(q,length modes,positions),labs,proofs)"
    and accepted: "check_lp_initial_triples_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
  by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_initial_triples_xml_sound[OF parsed accepted]) auto

theorem lp_finite_artifact_category_yes:
  assumes parsed: "parse_xml_string lp_finite_parser xml =
    Right (logic_to_program P,outs,fallback,names,filters,(q,length modes,positions),prf)"
    and accepted: "check_lp_finite_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and> lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
proof -
  have check: "check_lp_finite tp_rbt_impl dpp_rbt_impl (logic_to_program P)
    outs fallback names filters q (length modes) positions prf"
    using parsed accepted by (simp add: check_lp_finite_xml_def)
  show ?thesis
    by (rule logic_checked_query_transfer[OF modes];
      rule check_lp_tocl09_sound[OF tp_rbt_impl dpp_rbt_impl check]) auto
qed

ML \<open>
  val results = @{thms lp_finite_artifact_category_yes lp_constructor_category_yes lp_residual_constructor_category_yes lp_pidp_category_yes lp_pidp_mode_category_yes lp_simplify_category_yes lp_residual_category_yes lp_source_graph_category_yes lp_seg_category_yes lp_initial_triples_category_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "Pure LP YES families: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("Pure LP YES families: unexpected oracles: " ^ commas unexpected)
  val _ = warning ("Pure LP YES family oracle dependencies: " ^ commas names)
\<close>
end
