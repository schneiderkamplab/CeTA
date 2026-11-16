theory LP_Prolog_Scalar_Operations
 imports LP_Prolog_Binary64_Evaluation
begin

text \<open>Extend certificate evaluation with the integer-only operations already
specified by the source profile. Undefined division and floating operands are
rejected; the source operation itself is unchanged.\<close>

definition lpp_scalar_integer_binary_name where
 "lpp_scalar_integer_binary_name f =
   (f\<in>{''2:prolog_data_2f2f'',''2:prolog_data_6d6f64''})"
definition lpp_scalar_binary_name where
 "lpp_scalar_binary_name f = (lpp_machine_binary_name f \<or> lpp_scalar_integer_binary_name f)"
fun lpp_scalar_binary where
 "lpp_scalar_binary f (LPPMachineInteger n) (LPPMachineInteger m) =
   (if f=''2:prolog_data_2f2f'' then
      (if m=0 then None else Some (LPPMachineInteger (lpp_trunc_div n m)))
    else if f=''2:prolog_data_6d6f64'' then
      (if m=0 then None else Some (LPPMachineInteger (n mod m)))
    else lpp_machine_binary f (LPPMachineInteger n) (LPPMachineInteger m))"
| "lpp_scalar_binary f a b =
   (if lpp_scalar_integer_binary_name f then None else lpp_machine_binary f a b)"

lemma lpp_scalar_binary_valid:
 "lpp_scalar_binary f a b=Some v \<Longrightarrow> lpp_machine_valid v"
 by (cases a; cases b) (auto split: if_splits dest: lpp_machine_binary_valid lpp_machine_float_binary_valid)

lemma lpp_scalar_binary_profile:
 assumes "lpp_machine_valid a" "lpp_machine_valid b" "lpp_scalar_binary_name f"
 shows "lpp_binary64_profile_operation fallback (LPCUser f)
   [lpp_machine_value a,lpp_machine_value b] =
   map_option lpp_machine_value (lpp_scalar_binary f a b)"
 using assms
 by (cases a; cases b)
   (auto simp: lpp_scalar_binary_name_def lpp_scalar_integer_binary_name_def
     lpp_binary64_profile_operation_def lpp_binary64_fallback_def
     lpp_machine_binary_name_def lpp_machine_decode_value
     lpp_stable_decode_integer_literal lpp_stable_decode_binary64 split: if_splits)

ML \<open>
val checked = [@{thm lpp_scalar_binary_valid}, @{thm lpp_scalar_binary_profile}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar integer operation dependency" else ();
\<close>
end
