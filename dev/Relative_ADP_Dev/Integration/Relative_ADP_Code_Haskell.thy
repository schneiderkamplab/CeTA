theory Relative_ADP_Code_Haskell
  imports Relative_ADP_Ceta
begin

ML \<open>
val (modules, _) = Code_Target.produce_code @{context} false
  [@{const_name certify_proof_integrated}, @{const_name Certified},
   @{const_name Unsupported}, @{const_name Error}, @{const_name Inl},
   @{const_name Inr}, @{const_name nat_of_integer}, @{const_name literal.explode}]
  "Haskell" "Ceta_Relative" NONE []
val root = Resources.master_directory @{theory} +
  Path.explode "../../../generated/Haskell"
val _ = List.app (fn (names, bytes) =>
  Bytes.write (Path.appends (root :: map Path.basic names)) bytes) modules
\<close>

end
