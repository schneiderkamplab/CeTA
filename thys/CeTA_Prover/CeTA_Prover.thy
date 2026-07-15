theory CeTA_Prover 
  imports
    Containers.Set_Impl
    CR.Okui_Commutation_Automation
begin

derive (eq) ceq "term" 
derive (compare) ccompare "term"
derive (rbt) set_impl "term"

definition apply_subst_list where "apply_subst_list sigma (t :: (String.literal, String.literal)term) = t \<cdot> mk_subst Var sigma"

export_code 
  (* algorithms *)
  iterative_comm_solver 
  iterative_reach_solver 
  apply_subst_list 
  rewr_reconstruct_pos_from_1
  (* constructors *)
  Inl Var Fail CP_Reach_Cert 
  in Haskell module_name CeTA_Prover.Generated.CeTA_Prover 

end
