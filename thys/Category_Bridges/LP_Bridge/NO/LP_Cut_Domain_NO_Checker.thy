theory LP_Cut_Domain_NO_Checker
  imports LP_Cut_Domain_NO_Canonical
begin

lemma cut_back_ground: "logic_ground (cut_term_back t) = ground t"
  by (induct t) (auto simp: list_all_iff)

context cut_runtime_domain
begin

theorem canonical_no_certificate:
  assumes checked: "lpc_no_check_source fuel P q modes argv a before after initial_steps steps"
  shows "\<not> logic_cut_terminates_in (\<lambda>t. D (cut_tree t)) (cut_program_back P) q modes"
proof -
  have native: "\<not> SN_on (mgu_source P)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
    and lengths: "length argv=length modes"
    and ground: "list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes)"
    using no_check_source_sound[OF checked] by blast+
  obtain s where initial: "s 0 = [LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]"
    and steps: "\<forall>n. (s n,s (Suc n))\<in>mgu_source P"
    using native unfolding SN_on_def by blast
  have query: "logic_query (LogicUser q) modes (LogicUser q,map cut_term_back argv)"
    using lengths ground
    by (simp add: logic_query_def zip_map1 list_all_iff cut_back_ground case_prod_unfold)
  have start: "cut_state_back (s 0) =
    [LogicGoals [LogicAtom (LFun (LogicUser q) (map logic_embed (map cut_term_back argv)))]]"
    using initial by (simp add: map_map o_def cut_back_finite)
  have run: "\<forall>n. logic_cut_step (\<lambda>t. D (cut_tree t)) (cut_program_back P)
    (cut_state_back (s n)) (cut_state_back (s (Suc n)))"
    by (intro allI; rule canonical_no_step; rule spec[OF steps])
  show ?thesis unfolding logic_cut_terminates_in_def
    by (simp only: not_not; rule exI[of _ "map cut_term_back argv"];
      rule exI[of _ "\<lambda>n. cut_state_back (s n)"])
      (use query start run in blast)
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
  shows "\<not> logic_cut_terminates_in (\<lambda>t. D (cut_tree t)) P q modes"
proof -
  have check: "lpc_no_check_source fuel (cut_program P) q modes argv a before after initial_steps steps"
    using parsed checked by (simp add: check_lpc_no_xml_def)
  show ?thesis using canonical_no_certificate[OF check] by simp
qed
end

corollary lp_cut_source_finite_no:
  assumes "parse_xml_string lpc_no_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    "check_lpc_no_xml xml"
  shows "\<not> lp_cut_finite_terminates P q modes"
  using domain_canonical_xml_no[OF finite_cut.cut_runtime_domain_axioms assms]
  by (simp add: lp_cut_finite_terminates_def cut_finite_domain_iff)

corollary lp_cut_source_rational_no:
  assumes "parse_xml_string lpc_no_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    "check_lpc_no_xml xml"
  shows "\<not> lp_cut_rational_terminates P q modes"
  using domain_canonical_xml_no[OF rational_cut.cut_runtime_domain_axioms assms]
  by (simp add: lp_cut_rational_terminates_def cut_rational_runtime_def)

lemma cut_unrestricted_runtime:
  "cut_runtime_domain (\<lambda>t :: ('f lp_cut_symbol,string) lp_iterm. True)"
  by unfold_locales (simp_all add: list_all_iff)

corollary lp_cut_source_infinite_no:
  assumes "parse_xml_string lpc_no_certificate_parser xml =
    Right (cut_program P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    "check_lpc_no_xml xml"
  shows "\<not> lp_cut_infinite_terminates P q modes"
  using domain_canonical_xml_no[OF cut_unrestricted_runtime assms]
  by (simp add: lp_cut_infinite_terminates_def)

ML \<open>
  val thms = [@{thm lp_cut_source_finite_no}, @{thm lp_cut_source_rational_no}, @{thm lp_cut_source_infinite_no}];
  val _ = if Thm_Deps.has_skip_proof thms then error "Admitted NO bridge" else ();
  val allowed = ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"];
  val _ = List.app (fn th =>
    let val oracles = Thm_Deps.all_oracles [th] |> map (#1 o #1)
    in if forall (fn n => member (op =) allowed n) oracles then ()
       else error ("Unexpected oracle: " ^ commas oracles);
       warning ((#1 (Thm.get_name_hint th)) ^ " oracle dependencies: " ^ commas oracles)
    end) thms;
\<close>

end
