theory LP_Prolog_Binary64_Actions
 imports LP_Prolog_Binary64_Steps
begin

fun lpp_machine_is_integer where
 "lpp_machine_is_integer (LPPMachineInteger n)=True"
| "lpp_machine_is_integer (LPPMachineFloat b)=False"

lemma lpp_machine_integer_test:
 assumes "lpp_machine_valid v"
 shows "lpp_stable_source_builtin operation ''1:integer'' [lpp_machine_value v]
   (if lpp_machine_is_integer v then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
 using assms
 by (cases v)
   (auto simp: lpp_stable_source_builtin_def lpp_finite_source_builtin_def
      lpp_integer_test_outcome_def lpp_is_integer_def lpp_binary64_not_integer)

datatype lpp_machine_no_action = LPPMBase lpp_ground_integer_no_action |
 LPPMIs lpp_machine_expression |
 LPPMCompare lpp_machine_expression lpp_machine_expression bool |
 LPPMInteger lpp_machine_scalar

fun lpp_machine_no_step where
 "lpp_machine_no_step fuel P s (LPPMBase action) t = lpp_ground_integer_no_step fuel P s action t"
| "lpp_machine_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es) (LPPMIs e) t =
   (f=''2:is'' \<and> b=lpp_machine_expression_term e \<and>
    (case lpp_machine_evaluate e of None \<Rightarrow> False | Some v \<Rightarrow>
     t=(case lpp_machine_unifier a v of None \<Rightarrow> es
       | Some mu \<Rightarrow> LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>mu)) gs)#es)))"
| "lpp_machine_no_step fuel P s (LPPMIs e) t = False"
| "lpp_machine_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es) (LPPMCompare left right held) t =
   (a=lpp_machine_expression_term left \<and> b=lpp_machine_expression_term right \<and>
    (case (lpp_source_comparison f,lpp_machine_evaluate left,lpp_machine_evaluate right) of
      (Some (comparison,reversed),Some x,Some y) \<Rightarrow>
       (let (n,d)=lpp_machine_fraction (if reversed then y else x);
            (m,e)=lpp_machine_fraction (if reversed then x else y)
        in held=lpp_integer_compare comparison (n * e) (m * d))
     | _ \<Rightarrow> False) \<and> t=(if held then LPCGoals gs#es else es))"
| "lpp_machine_no_step fuel P s (LPPMCompare left right held) t = False"
| "lpp_machine_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs)#es) (LPPMInteger v) t =
   (f=''1:integer'' \<and> a=lpp_machine_term v \<and> lpp_machine_valid v \<and>
    t=(if lpp_machine_is_integer v then LPCGoals gs#es else es))"
| "lpp_machine_no_step fuel P s (LPPMInteger v) t = False"

end
