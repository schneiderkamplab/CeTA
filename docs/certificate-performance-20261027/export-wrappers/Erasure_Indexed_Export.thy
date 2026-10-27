theory Erasure_Indexed_Export
 imports "/work/dfm/festschrift/CeTA-consolidated/thys/Conditional_Ordinary/Conditional_Erasure" "/work/dfm/festschrift/CeTA-consolidated/thys/Usable_Rules_Membership/Usable_Rules_Membership" "/work/dfm/festschrift/CeTA-consolidated/thys/Certificate_Performance/Certificate_Performance"
begin
ML \<open>
val _ = if Thm_Deps.has_skip_proof [@{thm check_ur_closed_term_set_eq}, @{thm check_ur_P_closed_rm_af_indexed_code}] then error "Untrusted optimization" else ();
val (modules, _) = Code_Target.produce_code @{context} true [@{const_name check_conditional_erasure_xml}] "Haskell" "Conditional_Erasure_Generated" NONE [];
val _ = List.app (fn (names, content) => Bytes.write (Path.append (Path.explode "/work/dfm/festschrift/CeTA-consolidated/target/certificate-performance-20261027/erasure-indexed") (Path.make names)) content) modules;
\<close>
end
