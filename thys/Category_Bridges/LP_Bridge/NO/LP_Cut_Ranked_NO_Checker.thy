theory LP_Cut_Ranked_NO_Checker
  imports LP_Cut_Ranked_NO LP_Cut_Domain_NO_Checker
begin

lemma cut_rank_ground[simp]: "logic_ground (cut_rank_term t) = logic_ground t"
  by (induct t) (auto simp: list_all_iff)

context cut_runtime_domain
begin

theorem ranked_no_certificate:
  assumes checked: "lpc_no_check_source fuel P q modes argv a before after initial_steps steps"
    and shape: "cut_program_shape P"
    and program: "cut_control_program (cut_program_back P)"
    and arguments: "list_all cut_control_term (map cut_term_back argv)"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
  shows "\<not> logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t)))
    (cut_rank_program (cut_program_back P)) (q,length modes) modes"
proof -
  obtain sequence where initial:
      "sequence 0 = [LogicGoals [LogicAtom (LAtom (q,length modes)
        (map logic_embed (map cut_rank_term (map cut_term_back argv))))]]"
    and transitions: "\<And>n. logic_cut_step snd (\<lambda>u. D (cut_tree (cut_unrank_tree u)))
      (cut_rank_program (cut_program_back P)) (sequence n) (sequence (Suc n))"
    by (rule ranked_no_checked_run[OF checked shape program arguments projection]) blast+
  have lengths: "length argv=length modes"
    and ground: "list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes)"
    using checked by (auto simp: lpc_no_check_source_def)
  have query: "logic_query (logic_symbol_arity snd) (LogicUser (q,length modes)) modes
      (LAtom (LogicUser (q,length modes)) (map cut_rank_term (map cut_term_back argv)))"
    using lengths ground arguments
    by (simp add: logic_query_def zip_map1 list_all_iff cut_back_ground case_prod_unfold cut_control_term_def)
  show ?thesis unfolding logic_cut_terminates_in_def
    by (simp only: not_not; rule exI[of _ "map cut_rank_term (map cut_term_back argv)"]; rule exI[of _ sequence])
      (use query initial transitions in blast)
qed
end

text \<open>The boundary validates ordinary-predicate shapes and fixed control
arities, including witness arguments. Parsing a general term is not this check.
No certificate syntax or native checker representation changes.\<close>
definition cut_ranked_no_input :: "(string,string) lp_cut_program \<Rightarrow>
    (string lp_cut_symbol,string) term list \<Rightarrow> bool" where
  "cut_ranked_no_input P argv \<longleftrightarrow> cut_program_shape P \<and>
    cut_control_program (cut_program_back P) \<and>
    list_all cut_control_term (map cut_term_back argv)"
definition check_lpc_ranked_no_xml :: "string \<Rightarrow> bool" where
  "check_lpc_ranked_no_xml xml \<longleftrightarrow> check_lpc_no_xml xml \<and>
    (case parse_xml_string lpc_no_certificate_parser xml of
      Left e \<Rightarrow> False |
      Right (P,q,modes,fuel,argv,a,before,after,initial_steps,steps) \<Rightarrow> cut_ranked_no_input P argv)"

lemma logic_cut_step_domain_cong:
  assumes domains: "(\<lambda>t. D t \<and> logic_tree_arity_correct (logic_symbol_arity A) t) =
    (\<lambda>t. E t \<and> logic_tree_arity_correct (logic_symbol_arity A) t)"
  shows "logic_cut_step A D P s t = logic_cut_step A E P s t"
  by (subst (1 2) logic_cut_step.simps) (simp only: domains)
lemma logic_cut_termination_domain_cong:
  assumes domains: "(\<lambda>t. D t \<and> logic_tree_arity_correct (logic_symbol_arity A) t) =
    (\<lambda>t. E t \<and> logic_tree_arity_correct (logic_symbol_arity A) t)"
  shows "logic_cut_terminates_in A D P p modes = logic_cut_terminates_in A E P p modes"
  by (simp add: logic_cut_terminates_in_def logic_cut_step_domain_cong[OF domains])

lemma ranked_xml_no:
  assumes domain: "cut_runtime_domain D"
    and parsed: "parse_xml_string lpc_no_certificate_parser xml =
      Right (P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_ranked_no_xml xml"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
  shows "\<not> logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t)))
    (cut_rank_program (cut_program_back P)) (q,length modes) modes"
  using cut_runtime_domain.ranked_no_certificate[OF domain] parsed checked projection
  by (auto simp: check_lpc_ranked_no_xml_def check_lpc_no_xml_def cut_ranked_no_input_def)

corollary lp_cut_ranked_finite_no:
  assumes parsed: "parse_xml_string lpc_no_certificate_parser xml =
      Right (P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_ranked_no_xml xml"
  shows "\<not> lp_cut_finite_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
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
  show ?thesis using ranked_xml_no[OF finite_cut.cut_runtime_domain_axioms parsed checked projection]
    by (simp add: lp_cut_finite_terminates_def logic_cut_termination_domain_cong[OF domains])
qed

corollary lp_cut_ranked_rational_no:
  assumes parsed: "parse_xml_string lpc_no_certificate_parser xml =
      Right (P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_ranked_no_xml xml"
  shows "\<not> lp_cut_rational_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
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
  show ?thesis using ranked_xml_no[OF rational_cut.cut_runtime_domain_axioms parsed checked projection]
    by (simp add: lp_cut_rational_terminates_def logic_cut_termination_domain_cong[OF domains])
qed

corollary lp_cut_ranked_infinite_no:
  assumes parsed: "parse_xml_string lpc_no_certificate_parser xml =
      Right (P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_ranked_no_xml xml"
  shows "\<not> lp_cut_infinite_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
  using ranked_xml_no[OF cut_unrestricted_runtime parsed checked]
  by (simp add: lp_cut_infinite_terminates_def)

text \<open>Overloaded user names remain distinct ranked symbols. Malformed
ordinary heads and malformed control applications are rejected at the boundary.\<close>
lemma ranked_no_input_overloaded:
  "cut_ranked_no_input [(Fun (LPCUser ''p'') [],[]),
    (Fun (LPCUser ''p'') [Var ''X''],[])] []"
  by (simp add: cut_ranked_no_input_def cut_program_shape_def cut_control_program_def
    cut_program_back_def cut_control_term_def del: correct_term_iff)
lemma ranked_no_input_variable_head:
  "\<not> cut_ranked_no_input [(Var ''X'',[])] []"
  by (simp add: cut_ranked_no_input_def cut_program_shape_def)
lemma ranked_no_input_malformed_comma:
  "\<not> cut_ranked_no_input [(Fun (LPCUser ''p'') [Fun LPCComma []],[])] []"
  by (simp add: cut_ranked_no_input_def cut_program_shape_def cut_control_program_def
    cut_program_back_def cut_control_term_def del: correct_term_iff)
lemma ranked_no_input_malformed_witness:
  "\<not> cut_ranked_no_input [] [Fun LPCCallSymbol []]"
  by (simp add: cut_ranked_no_input_def cut_control_term_def del: correct_term_iff)

ML \<open>
  val results = @{thms lp_cut_ranked_finite_no lp_cut_ranked_rational_no lp_cut_ranked_infinite_no}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked cut NO checker: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Ranked cut NO checker: oracle dependency"
\<close>

end
