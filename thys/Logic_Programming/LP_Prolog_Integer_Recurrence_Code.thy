theory LP_Prolog_Integer_Recurrence_Code
  imports LP_Prolog_Integer_Recurrence_XML LP_Prolog_Numeric_Code_Setup
begin

text \<open>Importing the ITS parser also imports the Collections array code setup.
Restore the existing CeTA Haskell mapping after that import, as in
Proof_Checker.Ceta. The exported Array helper uses the Array constructor and
list-backed equations from Auxx.Diff_Array_Code_Haskell.\<close>
code_printing constant Array \<rightharpoonup> (Haskell) "Array.Array"
code_printing type_constructor array \<rightharpoonup> (Haskell) "Array.Array/ _"

end
