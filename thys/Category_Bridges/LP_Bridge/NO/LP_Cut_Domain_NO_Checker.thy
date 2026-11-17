theory LP_Cut_Domain_NO_Checker
  imports LP_Cut_Domain_NO_Canonical
begin

lemma cut_back_ground: "logic_ground (cut_term_back t) = ground t"
  by (induct t) (auto simp: list_all_iff)

context cut_runtime_domain
begin

theorem canonical_no_certificate:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_no_check_source fuel P q modes argv a before after initial_steps steps"
    and shape: "cut_program_shape P"
    and program: "logic_cut_problem A (cut_program_back P) q modes"
    and arguments: "list_all (arity_correct (logic_symbol_arity A)) (map cut_term_back argv)"
    and projection: "\<And>u. D (cut_tree u) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))"
  shows "\<not> logic_cut_terminates_in A (\<lambda>t. D (cut_tree t)) (cut_program_back P) q modes"
proof -
  obtain sequence :: "nat \<Rightarrow> ('f,('f logic_symbol,string) logic_tree) logic_choice list" where initial:
      "sequence 0 = [LogicGoals [LogicAtom (LAtom q (map logic_embed (map cut_term_back argv)))]]"
    and transitions: "\<And>n. logic_cut_step A (\<lambda>u. D (cut_tree u)) (cut_program_back P)
      (sequence n) (sequence (Suc n))"
    by (rule canonical_no_checked_run[OF checked shape program arguments projection]) blast+
  have lengths: "length argv=length modes" and modes: "length modes=A q"
    and ground: "list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes)"
    using checked program by (auto simp: lpc_no_check_source_def logic_cut_problem_def)
  have query: "logic_query (logic_symbol_arity A) (LogicUser q) modes
      (LAtom (LogicUser q) (map cut_term_back argv))"
    using lengths modes ground arguments
    by (simp add: logic_query_def zip_map1 list_all_iff cut_back_ground case_prod_unfold)
  show ?thesis unfolding logic_cut_terminates_in_def
    by (simp only: not_not; rule exI[of _ "map cut_term_back argv"]; rule exI[of _ sequence])
      (use query initial transitions in blast)
qed

end

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem domain_canonical_xml_no:
  assumes parsed: "parse_xml_string lpc_no_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_no_xml xml"
    and program: "logic_cut_problem A P q modes"
    and arguments: "list_all (arity_correct (logic_symbol_arity A)) (map cut_term_back argv)"
    and projection: "\<And>u. D (cut_tree u) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))"
  shows "\<not> logic_cut_terminates_in A (\<lambda>t. D (cut_tree t)) P q modes"
proof -
  have check: "lpc_no_check_source fuel (cut_program P) q modes argv a before after initial_steps steps"
    using parsed checked by (simp add: check_lpc_no_xml_def)
  show ?thesis using canonical_no_certificate[OF check cut_encoded_program_shape _ arguments projection]
    program by simp
qed
end

text \<open>These source-level corollaries expose source and query validity.
The concrete ranked boundary must establish both from validated input.\<close>

corollary lp_cut_source_finite_no:
  assumes parsed: "parse_xml_string lpc_no_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_no_xml xml"
    and program: "logic_cut_problem A P q modes"
    and arguments: "list_all (arity_correct (logic_symbol_arity A)) (map cut_term_back argv)"
  shows "\<not> lp_cut_finite_terminates A P q modes"
proof -
  have projection: "cut_finite_runtime (cut_tree u) \<Longrightarrow>
    cut_finite_runtime (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))" for u
    by (simp add: cut_finite_domain_iff logic_arity_project_finite)
  show ?thesis using domain_canonical_xml_no[OF finite_cut.cut_runtime_domain_axioms
      parsed checked program arguments projection]
    by (simp add: lp_cut_finite_terminates_def cut_finite_domain_iff)
qed

corollary lp_cut_source_rational_no:
  assumes parsed: "parse_xml_string lpc_no_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_no_xml xml"
    and program: "logic_cut_problem A P q modes"
    and arguments: "list_all (arity_correct (logic_symbol_arity A)) (map cut_term_back argv)"
  shows "\<not> lp_cut_rational_terminates A P q modes"
proof -
  have projection: "cut_rational_runtime (cut_tree u) \<Longrightarrow>
    cut_rational_runtime (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))" for u
    by (simp add: cut_rational_runtime_def logic_arity_project_rational)
  show ?thesis using domain_canonical_xml_no[OF rational_cut.cut_runtime_domain_axioms
      parsed checked program arguments projection]
    by (simp add: lp_cut_rational_terminates_def cut_rational_runtime_def)
qed

lemma cut_unrestricted_runtime:
  "cut_runtime_domain (\<lambda>t :: ('f lp_cut_symbol,string) lp_iterm. True)"
  by unfold_locales (simp_all add: list_all_iff)

corollary lp_cut_source_infinite_no:
  assumes parsed: "parse_xml_string lpc_no_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_no_xml xml"
    and program: "logic_cut_problem A P q modes"
    and arguments: "list_all (arity_correct (logic_symbol_arity A)) (map cut_term_back argv)"
  shows "\<not> lp_cut_infinite_terminates A P q modes"
  using domain_canonical_xml_no[OF cut_unrestricted_runtime parsed checked program arguments]
  by (simp add: lp_cut_infinite_terminates_def)

ML \<open>
  val results = @{thms lp_cut_source_finite_no lp_cut_source_rational_no lp_cut_source_infinite_no}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut source NO: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = if null names then () else error ("Cut source NO: oracle dependencies: " ^ commas names)
\<close>

end
