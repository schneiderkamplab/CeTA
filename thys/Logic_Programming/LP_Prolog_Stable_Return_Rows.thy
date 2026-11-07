theory LP_Prolog_Stable_Return_Rows
 imports LP_Prolog_Stable_Return_Call_Step
begin

type_synonym 'v lpp_return_call_receipt = "'v lpp_stable_numeric_call_receipt * 'v lpp_return_constraint list * string trans_var ia4_exp Formula.formula"

definition lpp_check_return_call_row where
  "lpp_check_return_call_row T summaries coordinates modes locations weak_system system
    triple receipt = (case (triple,receipt) of (((h,ps,b,gs),os),(weak_receipt,row_constraints,extra)) \<Rightarrow>
      lpp_check_stable_numeric_call_row T coordinates modes locations weak_system triple weak_receipt \<and>
      lpp_check_return_bindings summaries ps (lppsnc_bindings weak_receipt) row_constraints extra \<and>
      Transition (locations (fst h)) (locations (fst b)) (Conjunction [lppsnc_formula weak_receipt,extra])\<in>transition_rules system \<and>
      assertion system (locations (fst h))=Conjunction [] \<and>
      assertion system (locations (fst b))=Conjunction [])"

theorem lpp_checked_return_call_row_step:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_return_call_row T summaries coordinates modes locations weak_system system
      ((h,ps,b,gs),os) receipt"
    and program: "lpp_check_magnitude_program summaries P return_receipts"
    and success: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>a. lpp_success_atom_eval a eta) ps)"
    and known: "lpp_integer_known (map lpp_transfer_variable (lppsnc_facts (fst receipt))) eta"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and represented: "lpp_stable_numeric_call operation coordinates modes a pre"
  shows "\<exists>post. (State (lpp_integer_assignment pre) (locations (fst a)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system \<and>
    lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval b eta) post"
  by (rule lpp_checked_stable_return_call_step[where receipt="fst receipt" and extra_receipts="fst (snd receipt)" and extra="snd (snd receipt)", OF compatible _ program success _ _ _ _ known observations matching represented])
    (use checked in \<open>auto simp: lpp_check_return_call_row_def split: prod.splits\<close>)

end
