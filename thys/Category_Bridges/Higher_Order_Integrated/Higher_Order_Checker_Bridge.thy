theory Higher_Order_Checker_Bridge
  imports Category_Higher_Order_Bridge.Higher_Order_Sort_Extension
    Higher_Order_Filtered.Higher_Order_Filtered_CeTA
    Higher_Order_Call_Expansion.Higher_Order_Expansion_Code
    Higher_Order_Prefix.Higher_Order_Prefix_Schema
    Higher_Order_Guarded.Higher_Order_Guarded_Code
begin
text \<open>These are the concrete Boolean entry points used by the unified
higher-order adapters. Delegated first-order proofs are checked with the concrete
CeTA modules and certificate assumptions disabled. Parsing of the outer native
wire format remains outside these semantic theorems.\<close>

corollary higher_order_termination_YES:
  "ho_check_termination (map to_ho_type S) (map to_ho_rule R) w_cert
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_termination_sound by blast

corollary higher_order_application_YES:
  "ho_check_application (map to_ho_type S) (map to_ho_rule R) w_symbol
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_application_sound by blast

corollary higher_order_modular_YES:
  "ho_check_modular (map to_ho_type S) (map to_ho_rule R) w_cert
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_modular_sound by blast

corollary higher_order_meta_YES:
  "ho_check_meta (map to_ho_type S) (map to_ho_rule R) w_cert
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_meta_sound by blast

corollary higher_order_guarded_certificate_YES:
  "ho_check_guarded_certificate (map to_ho_type S) (map to_ho_rule R) w_cert
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_guarded_certificate_sound by blast

corollary higher_order_expansion_input_YES:
  "ho_check_expansion_input (map to_ho_type S) (map to_ho_rule R) w_ds w_efuel w_ps w_ms w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_expansion_input_sound by blast

corollary higher_order_prefix_schema_YES:
  "ho_check_prefix_schema (map to_ho_type S) (map to_ho_rule R) w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_prefix_schema_sound by blast

corollary higher_order_blocked_schema_YES:
  "ho_check_blocked_schema (map to_ho_type S) (map to_ho_rule R) w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_blocked_schema_sound by blast

corollary higher_order_lex_semantic_schema_YES:
  "ho_check_lex_semantic_schema (map to_ho_type S) (map to_ho_rule R) w_orders w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_lex_semantic_schema_sound by blast

corollary higher_order_functional_access_schema_YES:
  "ho_check_functional_access_schema (map to_ho_type S) (map to_ho_rule R) w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_functional_access_schema_sound by blast

corollary higher_order_component_schema_YES:
  "ho_check_component_schema (map to_ho_type S) (map to_ho_rule R) w_ps w_ms w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_component_schema_sound by blast

corollary higher_order_lambda_access_schema_YES:
  "ho_check_lambda_access_schema (map to_ho_type S) (map to_ho_rule R) w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_lambda_access_schema_sound by blast

corollary higher_order_semantic_schema_YES:
  "ho_check_semantic_schema (map to_ho_type S) (map to_ho_rule R) w_ps w_ms w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_semantic_schema_sound by blast

corollary higher_order_ceta_delegation_xml_YES:
  "ho_check_ceta_delegation_xml (map to_ho_type S) (map to_ho_rule R) w_F w_P w_ce w_ranks w_arities w_priorities w_sorts w_fuel w_xml
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_ceta_delegation_xml_sound by blast

corollary higher_order_ceta_semantic_delegation_xml_YES:
  "ho_check_ceta_semantic_delegation_xml (map to_ho_type S) (map to_ho_rule R) w_F w_P w_ce w_ps w_ms w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel w_xml
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_ceta_semantic_delegation_xml_sound by blast

corollary higher_order_ceta_filtered_delegation_xml_YES:
  "ho_check_ceta_filtered_delegation_xml (map to_ho_type S) (map to_ho_rule R) w_F w_P w_ce w_ranks w_arities w_priorities w_selections w_phases w_sorts w_fuel w_xml
    \<Longrightarrow> higher_order_terminates S R"
  unfolding higher_order_terminates_iff
  using ho_check_ceta_filtered_delegation_xml_sound by blast

corollary higher_order_loop_NO:
  "ho_check_loop (map to_ho_type S) w_V (map to_ho_rule R) w_A w_t w_ps
    \<Longrightarrow> \<not> higher_order_terminates S R"
  unfolding higher_order_nonterminates_iff
  by (meson ho_check_loop_sound)

corollary higher_order_embedding_NO:
  "ho_check_embedding (map to_ho_type S) w_V (map to_ho_rule R) w_A w_t w_ps w_C
    \<Longrightarrow> \<not> higher_order_terminates S R"
  unfolding higher_order_nonterminates_iff
  by (meson ho_check_embedding_sound)

corollary higher_order_plain_pump_NO:
  "ho_check_plain_pump (map to_ho_type S) w_V (map to_ho_rule R) w_A w_t w_ps w_C w_sigma
    \<Longrightarrow> \<not> higher_order_terminates S R"
  unfolding higher_order_nonterminates_iff
  by (meson ho_check_plain_pump_sound)

corollary higher_order_rule_pump_NO:
  "ho_check_rule_pump (map to_ho_type S) (map to_ho_rule R) w_index w_sigma
    \<Longrightarrow> \<not> higher_order_terminates S R"
  unfolding higher_order_nonterminates_iff
  by (meson ho_check_rule_pump_sound)


lemma higher_order_empty_terminates:
  "higher_order_terminates S []"
  using higher_order_termination_YES[where S=S and R="[]" and w_cert=HOEmpty] by simp

lemma higher_order_declared_sorts_iff:
  assumes "higher_order_declared_problem N S R"
  shows "higher_order_terminates_over_sorts N S R \<longleftrightarrow> higher_order_terminates S R"
proof (cases "N = 0")
  case True
  then have "R = []" using assms by (simp add: higher_order_declared_problem_def)
  then show ?thesis using True by (simp add: higher_zero_sorts_terminate higher_order_empty_terminates)
next
  case False
  then show ?thesis using assms higher_order_sorts_extension
    unfolding higher_order_declared_problem_def by blast
qed

lemma higher_order_to_declared_sorts:
  "higher_order_terminates S R \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  unfolding higher_order_terminates_def higher_order_terminates_over_sorts_def no_infinite_steps_def
  by blast

corollary higher_order_termination_YES_declared_sorts:
  "ho_check_termination (map to_ho_type S) (map to_ho_rule R) w_cert
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_termination_YES higher_order_to_declared_sorts by blast

corollary higher_order_application_YES_declared_sorts:
  "ho_check_application (map to_ho_type S) (map to_ho_rule R) w_symbol
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_application_YES higher_order_to_declared_sorts by blast

corollary higher_order_modular_YES_declared_sorts:
  "ho_check_modular (map to_ho_type S) (map to_ho_rule R) w_cert
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_modular_YES higher_order_to_declared_sorts by blast

corollary higher_order_meta_YES_declared_sorts:
  "ho_check_meta (map to_ho_type S) (map to_ho_rule R) w_cert
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_meta_YES higher_order_to_declared_sorts by blast

corollary higher_order_guarded_certificate_YES_declared_sorts:
  "ho_check_guarded_certificate (map to_ho_type S) (map to_ho_rule R) w_cert
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_guarded_certificate_YES higher_order_to_declared_sorts by blast

corollary higher_order_expansion_input_YES_declared_sorts:
  "ho_check_expansion_input (map to_ho_type S) (map to_ho_rule R) w_ds w_efuel w_ps w_ms w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_expansion_input_YES higher_order_to_declared_sorts by blast

corollary higher_order_prefix_schema_YES_declared_sorts:
  "ho_check_prefix_schema (map to_ho_type S) (map to_ho_rule R) w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_prefix_schema_YES higher_order_to_declared_sorts by blast

corollary higher_order_blocked_schema_YES_declared_sorts:
  "ho_check_blocked_schema (map to_ho_type S) (map to_ho_rule R) w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_blocked_schema_YES higher_order_to_declared_sorts by blast

corollary higher_order_lex_semantic_schema_YES_declared_sorts:
  "ho_check_lex_semantic_schema (map to_ho_type S) (map to_ho_rule R) w_orders w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_lex_semantic_schema_YES higher_order_to_declared_sorts by blast

corollary higher_order_functional_access_schema_YES_declared_sorts:
  "ho_check_functional_access_schema (map to_ho_type S) (map to_ho_rule R) w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_functional_access_schema_YES higher_order_to_declared_sorts by blast

corollary higher_order_component_schema_YES_declared_sorts:
  "ho_check_component_schema (map to_ho_type S) (map to_ho_rule R) w_ps w_ms w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_component_schema_YES higher_order_to_declared_sorts by blast

corollary higher_order_lambda_access_schema_YES_declared_sorts:
  "ho_check_lambda_access_schema (map to_ho_type S) (map to_ho_rule R) w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_lambda_access_schema_YES higher_order_to_declared_sorts by blast

corollary higher_order_semantic_schema_YES_declared_sorts:
  "ho_check_semantic_schema (map to_ho_type S) (map to_ho_rule R) w_ps w_ms w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_semantic_schema_YES higher_order_to_declared_sorts by blast

corollary higher_order_ceta_delegation_xml_YES_declared_sorts:
  "ho_check_ceta_delegation_xml (map to_ho_type S) (map to_ho_rule R) w_F w_P w_ce w_ranks w_arities w_priorities w_sorts w_fuel w_xml
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_ceta_delegation_xml_YES higher_order_to_declared_sorts by blast

corollary higher_order_ceta_semantic_delegation_xml_YES_declared_sorts:
  "ho_check_ceta_semantic_delegation_xml (map to_ho_type S) (map to_ho_rule R) w_F w_P w_ce w_ps w_ms w_ofuel w_ranks w_arities w_priorities w_sorts w_fuel w_xml
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_ceta_semantic_delegation_xml_YES higher_order_to_declared_sorts by blast

corollary higher_order_ceta_filtered_delegation_xml_YES_declared_sorts:
  "ho_check_ceta_filtered_delegation_xml (map to_ho_type S) (map to_ho_rule R) w_F w_P w_ce w_ranks w_arities w_priorities w_selections w_phases w_sorts w_fuel w_xml
    \<Longrightarrow> higher_order_terminates_over_sorts N S R"
  using higher_order_ceta_filtered_delegation_xml_YES higher_order_to_declared_sorts by blast

corollary higher_order_loop_NO_declared_sorts:
  "higher_order_declared_problem N S R \<Longrightarrow> ho_check_loop (map to_ho_type S) w_V (map to_ho_rule R) w_A w_t w_ps
    \<Longrightarrow> \<not> higher_order_terminates_over_sorts N S R"
  using higher_order_loop_NO higher_order_declared_sorts_iff by blast

corollary higher_order_embedding_NO_declared_sorts:
  "higher_order_declared_problem N S R \<Longrightarrow> ho_check_embedding (map to_ho_type S) w_V (map to_ho_rule R) w_A w_t w_ps w_C
    \<Longrightarrow> \<not> higher_order_terminates_over_sorts N S R"
  using higher_order_embedding_NO higher_order_declared_sorts_iff by blast

corollary higher_order_plain_pump_NO_declared_sorts:
  "higher_order_declared_problem N S R \<Longrightarrow> ho_check_plain_pump (map to_ho_type S) w_V (map to_ho_rule R) w_A w_t w_ps w_C w_sigma
    \<Longrightarrow> \<not> higher_order_terminates_over_sorts N S R"
  using higher_order_plain_pump_NO higher_order_declared_sorts_iff by blast

corollary higher_order_rule_pump_NO_declared_sorts:
  "higher_order_declared_problem N S R \<Longrightarrow> ho_check_rule_pump (map to_ho_type S) (map to_ho_rule R) w_index w_sigma
    \<Longrightarrow> \<not> higher_order_terminates_over_sorts N S R"
  using higher_order_rule_pump_NO higher_order_declared_sorts_iff by blast

ML \<open>
  val results = @{thms hs_declared_instance higher_order_declared_sorts_iff higher_order_termination_YES_declared_sorts higher_order_application_YES_declared_sorts higher_order_modular_YES_declared_sorts higher_order_meta_YES_declared_sorts higher_order_guarded_certificate_YES_declared_sorts higher_order_expansion_input_YES_declared_sorts higher_order_prefix_schema_YES_declared_sorts higher_order_blocked_schema_YES_declared_sorts higher_order_lex_semantic_schema_YES_declared_sorts higher_order_functional_access_schema_YES_declared_sorts higher_order_component_schema_YES_declared_sorts higher_order_lambda_access_schema_YES_declared_sorts higher_order_semantic_schema_YES_declared_sorts higher_order_ceta_delegation_xml_YES_declared_sorts higher_order_ceta_semantic_delegation_xml_YES_declared_sorts higher_order_ceta_filtered_delegation_xml_YES_declared_sorts higher_order_loop_NO_declared_sorts higher_order_embedding_NO_declared_sorts higher_order_plain_pump_NO_declared_sorts higher_order_rule_pump_NO_declared_sorts
    higher_step_iff higher_order_step_iff higher_order_terminates_iff
    higher_order_nonterminates_iff
    higher_order_termination_YES
    higher_order_application_YES
    higher_order_modular_YES
    higher_order_meta_YES
    higher_order_guarded_certificate_YES
    higher_order_expansion_input_YES
    higher_order_prefix_schema_YES
    higher_order_blocked_schema_YES
    higher_order_lex_semantic_schema_YES
    higher_order_functional_access_schema_YES
    higher_order_component_schema_YES
    higher_order_lambda_access_schema_YES
    higher_order_semantic_schema_YES
    higher_order_ceta_delegation_xml_YES
    higher_order_ceta_semantic_delegation_xml_YES
    higher_order_ceta_filtered_delegation_xml_YES
    higher_order_loop_NO
    higher_order_embedding_NO
    higher_order_plain_pump_NO
    higher_order_rule_pump_NO}
  val _ = if Thm_Deps.has_skip_proof results then error "Higher-order: admitted proof" else ()
  val names = Thm_Deps.all_oracles results
    |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Higher-order integrated oracle dependencies: " ^ commas names)
\<close>
end
