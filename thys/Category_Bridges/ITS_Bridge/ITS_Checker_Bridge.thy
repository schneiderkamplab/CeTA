theory ITS_Checker_Bridge
  imports ITS_Equivalence
begin

theorem its_checker_decision:
  "isOK (check_its4 P answer proof) \<Longrightarrow>
    its_terminates (its_translate (lts_of P)) = answer"
  using check_its4_sound its_termination_iff by blast
corollary its_checker_yes:
  "isOK (check_its4 P True proof) \<Longrightarrow> its_terminates (its_translate (lts_of P))"
  using its_checker_decision by blast
corollary its_checker_no:
  "isOK (check_its4 P False proof) \<Longrightarrow> \<not> its_terminates (its_translate (lts_of P))"
  using its_checker_decision by blast

text \<open>The serialized corollary binds the conclusion to the parser's exact
problem and answer. Correspondence with an original ARI file is a separate
frontend obligation.\<close>
corollary its_serialized_decision:
  assumes parsed: "parse_xml_string its4_cpf_parser xml = Right (P,answer,proof)"
    and accepted: "check_its4_string xml = Inr ()"
  shows "its_terminates (its_translate (lts_of P)) = answer"
proof (rule its_checker_decision)
  show "isOK (check_its4 P answer proof)"
    using accepted unfolding check_its4_string_def parsed
    by (cases "check_its4 P answer proof") auto
qed

ML \<open>
  val results = @{thms its_decode_encode its_encode_decode its_step_decode
    its_step_encode its_termination_iff its_checker_yes its_checker_no
    its_serialized_decision}
  val _ = if Thm_Deps.has_skip_proof results then error "ITS: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv"] names
  val _ = if null unexpected then ()
    else error ("ITS: unexpected oracle dependencies: " ^ commas unexpected)
  val _ = warning ("ITS category oracle dependencies: " ^ commas names)
\<close>
end
