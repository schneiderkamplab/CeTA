theory Conditional_Erasure_CPF4_Code
  imports Conditional_Ordinary.Conditional_Erasure
    Certificate_Performance.Certificate_Performance
begin

ML \<open>
val _ = if Thm_Deps.has_skip_proof [@{thm check_conditional_erasure_xml_sound}]
  then error "Conditional erasure soundness contains an admitted proof"
  else ();
\<close>

export_code check_conditional_erasure_xml literal.explode
  in Haskell module_name Conditional_Erasure_Generated

end
