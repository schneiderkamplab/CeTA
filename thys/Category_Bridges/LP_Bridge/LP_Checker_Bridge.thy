theory LP_Checker_Bridge
  imports LP_Representation Category_Specifications.LP_Infinite_Spec
begin

text \<open>The concrete checker instantiation disables certificate assumptions.
The parser-result premise identifies the exact program, query and certificate;
it is not supplied as a processor soundness hypothesis.\<close>
theorem lp_tocl09_category_yes:
  assumes parsed: "parse_xml_string lp_tocl09_parser xml =
    Right (logic_to_program P,outs,fallback,names,filters,(q,length modes,positions),prf)"
    and accepted: "check_lp_tocl09_xml xml"
    and modes: "set positions = {i. i<length modes \<and> modes!i}"
  shows "lp_finite_terminates P q modes \<and> lp_rational_terminates P q modes \<and>
    lp_infinite_terminates P q modes"
proof -
  have all: "logic_terminates_in D P q modes" for D
  proof (rule logic_native_termination)
    fix a :: "((string,nat list) lab, ((string,nat list) lab,string) fo_term) logic_atom"
    assume query: "logic_query q modes a"
    have len: "length (map to_term (snd a)) = length modes" using query
      by (simp add: logic_query_def)
    have gr: "ground (map to_term (snd a)!i)" if "i\<in>set positions" "i<length modes" for i
      using query modes that
      by (auto simp: logic_query_def list_all_iff set_zip logic_ground_translation; blast)
    have native: "SN_on (lp_ild (logic_to_program P))
      {[(q,map (\<lambda>t. lp_ieval t LPIVar) (map to_term (snd a)))]}"
      by (rule check_lp_tocl09_xml_sound[OF parsed accepted len gr])
    show "SN_on (lp_ild (logic_to_program P)) {logic_to_goals [logic_atom_map logic_embed a]}"
      using native query by (simp add: logic_to_goals_def logic_atom_map_def
        logic_query_def map_map o_def logic_embed_translation)
  qed
  show ?thesis using all unfolding lp_finite_terminates_def lp_rational_terminates_def lp_infinite_terminates_def by blast
qed

ML \<open>
  val results = @{thms logic_roundtrip logic_native_roundtrip
    logic_subst_translation logic_eval_translation logic_step_native
    logic_native_termination lp_tocl09_category_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "LP: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then ()
    else error ("LP: unexpected oracle dependencies: " ^ commas unexpected)
  val _ = warning ("LP category oracle dependencies: " ^ commas names)
\<close>
end
