theory LP_Prolog_Binary64_Actions
 imports LP_Prolog_Binary64_Steps LP_Prolog_NO_Probe_Definition LP_Prolog_NO_List_Definition LP_Prolog_NO_Permutation
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
 LPPMInteger lpp_machine_scalar | LPPMProbe nat nat | LPPMList bool |
 LPPMResolvePermute nat "string list" "(string lp_cut_symbol,string) term list" "(string * string) list"

fun lpp_machine_no_step_action where
 "lpp_machine_no_step_action fuel P (LPPMBase action) s t = lpp_ground_integer_no_step fuel P s action t"
| "lpp_machine_no_step_action fuel P (LPPMIs e) s t =
   (case s of LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es \<Rightarrow>
   (f=''2:is'' \<and> b=lpp_machine_expression_term e \<and>
    (case lpp_machine_evaluate e of None \<Rightarrow> False | Some v \<Rightarrow>
     t=(case lpp_machine_unifier a v of None \<Rightarrow> es
       | Some mu \<Rightarrow> LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>mu)) gs)#es)))
    | _ \<Rightarrow> False)"
| "lpp_machine_no_step_action fuel P (LPPMCompare left right held) s t =
   (case s of LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es \<Rightarrow>
   (a=lpp_machine_expression_term left \<and> b=lpp_machine_expression_term right \<and>
    (case (lpp_source_comparison f,lpp_machine_evaluate left,lpp_machine_evaluate right) of
      (Some (comparison,reversed),Some x,Some y) \<Rightarrow>
       (let (n,d)=lpp_machine_fraction (if reversed then y else x);
            (m,e)=lpp_machine_fraction (if reversed then x else y)
        in held=lpp_integer_compare comparison (n * e) (m * d))
     | _ \<Rightarrow> False) \<and> t=(if held then LPCGoals gs#es else es))
    | _ \<Rightarrow> False)"
| "lpp_machine_no_step_action fuel P (LPPMInteger v) s t =
   (case s of LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs)#es \<Rightarrow>
   (f=''1:integer'' \<and> a=lpp_machine_term v \<and> lpp_machine_valid v \<and>
    t=(if lpp_machine_is_integer v then LPCGoals gs#es else es))
    | _ \<Rightarrow> False)"

| "lpp_machine_no_step_action fuel P (LPPMProbe m n) s t = lpp_no_plain_probe m n s t"

| "lpp_machine_no_step_action fuel P (LPPMList held) s t = lpp_no_plain_list fuel held s t"

| "lpp_machine_no_step_action fuel P (LPPMResolvePermute k V images swaps) s t =
    lpp_no_plain_permutation fuel P k V images swaps s t"

abbreviation lpp_machine_no_step where
 "lpp_machine_no_step fuel P s action t \<equiv> lpp_machine_no_step_action fuel P action s t"

end
