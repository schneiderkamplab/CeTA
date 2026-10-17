(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015, 2017, 2020)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Code_Haskell_Configuration
  imports
    Proof_Checker.Ceta
    Proof_Checker.Version
begin

(* export code in separate modules, so that module_merge program can determine SCCs

export_code certify_proof Certified Unsupported Error Inl Inr version
  nat_of_integer
  literal.explode
  in Haskell file For_Module_Merge

*)

(* automatically generated module names via module_merge,
   where circular imports are resolved *)

(* note that using separate module names will
  - speed up Haskell compilation time: factor 0.66
  - slightly increase execution time of CeTA: factor 1.07


  deactivate separate compiliation be putting the below
  code_identifer parts into comment and by adjusting
  Main by deleting some explicit imports (those without comments)
*)
code_identifier
   code_module "Ceta_Verifier" \<rightharpoonup> (Haskell) "Ceta"

code_identifier
   code_module "Quasi_Order" \<rightharpoonup> (Haskell) "Quasi_Order"
 | code_module "Lattices" \<rightharpoonup> (Haskell) "Quasi_Order"
 | code_module "Orderings" \<rightharpoonup> (Haskell) "Quasi_Order"

code_identifier
   code_module "Arith" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Product_Type" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Option" \<rightharpoonup> (Haskell) "Arith"
 | code_module "List" \<rightharpoonup> (Haskell) "Arith"
 | code_module "RBT_Set2" \<rightharpoonup> (Haskell) "Arith"
 | code_module "RBT_Comparator_Impl" \<rightharpoonup> (Haskell) "Arith"
 | code_module "RBT_Impl" \<rightharpoonup> (Haskell) "Arith"
 | code_module "RBT_ext" \<rightharpoonup> (Haskell) "Arith"
 | code_module "List_Fusion" \<rightharpoonup> (Haskell) "Arith"
 | code_module "RBT_Mapping2" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Collection_Order" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Compare_Instances" \<rightharpoonup> (Haskell) "Arith"
 | code_module "String" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Char_ord" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Code_Abstract_Char" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Set_Linorder" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Finite_Set" \<rightharpoonup> (Haskell) "Arith"
 | code_module "DList_Set" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Collection_Eq" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Set" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Cardinality" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Set_Impl" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Collection_Enum" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Lexicographic_Order" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Unique_Factorization" \<rightharpoonup> (Haskell) "Arith"
 | code_module "GCD" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Max_Polynomial_Aux" \<rightharpoonup> (Haskell) "Arith"
 | code_module "Norms" \<rightharpoonup> (Haskell) "Arith"

code_identifier
   code_module "Matrix" \<rightharpoonup> (Haskell) "Matrix"
 | code_module "Matrix_IArray_Impl" \<rightharpoonup> (Haskell) "Matrix"

code_identifier
   code_module "Mapping_Impl" \<rightharpoonup> (Haskell) "Mapping"
 | code_module "Mapping" \<rightharpoonup> (Haskell) "Mapping"

code_identifier
   code_module "Linear_Poly_Maps" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Rat" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Matrix_Core_Order" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Term" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Term_More" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Term_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Shows_Literal" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Container_Setup" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Tree_Automata_Autoref_Setup" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Tree_Automata" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Ground_Context_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Show_Instances" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Unification_String" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Unification" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Ground_Context" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Labelings_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Formula" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Sorted_Algebra" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Integer_Arithmetic" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Show_Literal_Polynomial" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Forbidden_Patterns" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Subterm_and_Context" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Cooperation_Program" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "LTS" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Linear_Polynomial" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Argument_Filter" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Term_Order_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Trs" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Matching" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Matching_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Trs_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Complexity" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "SN_Order_Carrier" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Archimedean_Field" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Multihole_Context" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Multihole_Context_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "QDelta" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Simplex_Algebra" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Simplex" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Abstract_Linear_Poly" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Real" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Real_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Sqrt_Babylonian" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "NthRoot_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Real_Unique_Impl" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Prime_Product" \<rightharpoonup> (Haskell) "Term_Rewriting"
 | code_module "Missing_Lemmas" \<rightharpoonup> (Haskell) "Term_Rewriting"

code_identifier
   code_module "Transcendental" \<rightharpoonup> (Haskell) "Transcendental"
 | code_module "Real_Vector_Spaces" \<rightharpoonup> (Haskell) "Transcendental"

code_identifier
   code_module "Nonloop_SRS_Impl" \<rightharpoonup> (Haskell) "Nonloop_SRS"
 | code_module "Nonloop_SRS" \<rightharpoonup> (Haskell) "Nonloop_SRS"

code_identifier
   code_module "Tree_Automata_NF_Impl" \<rightharpoonup> (Haskell) "Tree_Automata_NF"
 | code_module "Tree_Automata_NF" \<rightharpoonup> (Haskell) "Tree_Automata_NF"


end
