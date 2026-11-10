theory LP_Finite_NO_Checkers
  imports LP_Finite_NO_Canonical LP_Finite_Neutral_Witness
begin

lemma lp_checked_finite_witness_no:
  assumes modes: "set positions={i. i<length modes \<and> modes!i}"
    and witness: "\<exists>ts. length ts=length modes \<and>
      (\<forall>i\<in>set positions. ground (ts!i)) \<and>
      \<not>SN_on (lp_ld (logic_to_program P)) {[(q,ts)]}"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
proof -
  obtain ts where len: "length ts=length modes"
    and gr: "\<forall>i\<in>set positions. ground (ts!i)"
    and bad: "\<not>SN_on (lp_ld (logic_to_program P)) {[(q,ts)]}"
    using witness by blast
  show ?thesis by (rule lp_finite_witness_canonical_no[OF bad len]) (use modes gr in auto)
qed

theorem lp_source_loop_category_no:
  assumes parsed: "parse_xml_string lp_source_loop_parser xml =
    Right (logic_to_program P,(q,length modes,positions),c,seed,bindings)"
    and accepted: "check_lp_nontermination_xml xml"
    and modes: "set positions={i. i<length modes \<and> modes!i}"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
  by (rule lp_checked_finite_witness_no[OF modes])
    (use check_lp_nontermination_xml_sound[OF parsed accepted] modes in
      \<open>auto simp: list_all_iff\<close>)

theorem lp_source_trace_category_no:
  assumes parsed: "parse_xml_string lp_source_trace_parser xml =
    Right (logic_to_program P,(q,length modes,positions),seed,h,steps,bindings)"
    and accepted: "check_lp_source_trace_xml xml"
    and modes: "set positions={i. i<length modes \<and> modes!i}"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
proof -
  have checked: "lp_source_trace_check (logic_to_program P) q (length modes) positions h steps bindings"
    using parsed accepted by (simp add: check_lp_source_trace_xml_def)
  show ?thesis by (rule lp_checked_finite_witness_no[OF modes])
    (use lp_source_trace_check_finite_sound[OF checked] modes in \<open>auto simp: list_all_iff\<close>)
qed

theorem lp_source_unify_category_no:
  assumes parsed: "parse_xml_string lp_source_unify_parser xml =
    Right (logic_to_program P,(q,length modes,positions),a0,entry_steps,steps,bindings)"
    and accepted: "check_lp_source_unify_xml xml"
    and modes: "set positions={i. i<length modes \<and> modes!i}"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
proof -
  have checked: "lp_source_unify_check (logic_to_program P) q (length modes) positions a0 entry_steps steps bindings"
    using parsed accepted by (simp add: check_lp_source_unify_xml_def)
  show ?thesis by (rule lp_checked_finite_witness_no[OF modes])
    (use lp_source_unify_check_finite_sound[OF checked] in auto)
qed

theorem lp_source_neutral_category_no:
  assumes parsed: "parse_xml_string lp_source_neutral_parser xml =
    Right (logic_to_program P,(q,length modes,positions),a0,entry_steps,c,Is,sb,rb)"
    and accepted: "check_lp_source_neutral_xml xml"
    and modes: "set positions={i. i<length modes \<and> modes!i}"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
proof -
  have checked: "lp_source_neutral_check (logic_to_program P) q (length modes) positions a0 entry_steps c Is sb rb"
    using parsed accepted by (simp add: check_lp_source_neutral_xml_def)
  show ?thesis by (rule lp_checked_finite_witness_no[OF modes])
    (use lp_finite_source_neutral_check_sound[OF checked] in auto)
qed

ML \<open>
  val results = @{thms lp_source_loop_category_no lp_source_trace_category_no
    lp_source_unify_category_no lp_source_neutral_category_no}
  val _ = if Thm_Deps.has_skip_proof results then error "Pure LP NO: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("Pure LP NO: unexpected oracles: " ^ commas unexpected)
  val _ = warning ("Pure LP loop/trace/unify/neutral NO oracle dependencies: " ^ commas names)
\<close>
end
