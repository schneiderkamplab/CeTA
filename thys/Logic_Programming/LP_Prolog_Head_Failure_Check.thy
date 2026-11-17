theory LP_Prolog_Head_Failure_Check
 imports LP_Prolog_Pattern_Failure LP_Prolog_Head_Apart LP_Prolog_Scalar_Recurrence_Failure_Check
begin

datatype lpp_head_failure =
 LPPVariableFailure "string list * lpp_scalar_guard list * lpp_scalar_guard"
 | LPPHeadApart nat nat
 | LPPPatternFailure "string list" "string option list" "lpp_scalar_guard list" lpp_scalar_guard

fun lpp_check_head_failure where
 "lpp_check_head_failure P q observations d (LPPVariableFailure receipt) =
   lpp_check_scalar_failure P q observations d receipt"
| "lpp_check_head_failure P q observations d (LPPHeadApart i j) =
   lpp_head_apart_check P q observations d i j"
| "lpp_check_head_failure P q observations d (LPPPatternFailure H constants guards failure) =
   lpp_check_pattern_failure P q observations d H constants guards failure"

lemma lpp_check_head_failure_sound:
 assumes checked: "lpp_check_head_failure P q observations d receipt"
   and observed: "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations actuals"
 shows "(LPCClause (LPCAtom (LPIFun (LPCUser q) actuals)#gs) d mark#saved,saved)\<in>
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
 using checked
 by (cases receipt)
    (auto intro: lpp_check_scalar_failure_sound[OF _ observed]
      lpp_head_apart_failure[OF _ observed] lpp_check_pattern_failure_sound[OF _ observed])

ML \<open>
val checked = [@{thm lpp_check_head_failure_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted head failure assembly" else ();
\<close>
end
