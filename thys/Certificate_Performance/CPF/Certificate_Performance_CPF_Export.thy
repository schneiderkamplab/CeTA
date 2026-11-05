theory Certificate_Performance_CPF_Export
 imports "Usable_Rules_CPF_Export.Usable_Rules_CPF_Export"
   "Certificate_Performance.Certificate_Performance"
begin

text \<open>Repeated final states describe the same right-extension obligations.
  Deduplicate them only for this universal check; retain the paired initial
  language entries in the certificate and all other checks.\<close>
lemma rfc_right_distinct_tails_code [code]:
  fixes TA rel tails qs R
  shows
  "rfc_matchbox_ext_right_indexed_impl TA rel tails qs R =
    list_all
      (rfc_rule_matchbox_ext_right_indexed_impl TA rel (remdups tails) qs) R"
  unfolding rfc_matchbox_ext_right_indexed_impl_def
  by (simp add: rfc_rule_matchbox_ext_right_indexed_impl_eq
      rfc_rule_matchbox_ext_right_impl_def list_all_iff
      split: option.splits prod.splits)

ML \<open>
val _ = if Thm_Deps.has_skip_proof [@{thm rfc_right_distinct_tails_code}]
  orelse not (null (Thm_Deps.all_oracles [@{thm rfc_right_distinct_tails_code}]))
  then error "RFC tail refinement must be kernel checked without oracles"
  else ();
\<close>

export_code certify_proof_integrated Certified Unsupported Error Inl Inr
  nat_of_integer literal.explode in Haskell module_name Ceta_Relative
end
