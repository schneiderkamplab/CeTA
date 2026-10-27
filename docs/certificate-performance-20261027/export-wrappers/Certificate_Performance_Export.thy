theory Certificate_Performance_Export
imports "Usable_Rules_CPF_Export.Usable_Rules_CPF_Export" "/work/dfm/festschrift/CeTA-consolidated/thys/Certificate_Performance/Certificate_Performance"
begin
ML \<open>
val audited = [@{thm xml_do_prepare}, @{thm xml_do_or_prepare}, @{thm normalized_nodes_code(2)}, @{thm parse_xml_string_fused_code}];
val _ = if Thm_Deps.has_skip_proof audited then error "Untrusted parser export" else ();
val (modules, _) = Code_Target.produce_code @{context} false [@{const_name certify_proof_integrated}, @{const_name Certified}, @{const_name Unsupported}, @{const_name Error}, @{const_name Inl}, @{const_name Inr}, @{const_name nat_of_integer}, @{const_name String.explode}] "Haskell" "Ceta_Relative" NONE [];
val _ = List.app (fn (names, content) => Bytes.write (Path.append (Path.explode "/work/dfm/festschrift/CeTA-consolidated/target/certificate-performance-20261027/cpf-final-export") (Path.make names)) content) modules;
\<close>
end
