theory LP_Prolog_Binary64_Evaluation
 imports LP_Prolog_Binary64_Operations
begin

definition lpp_machine_binary_name where
 "lpp_machine_binary_name f = (f\<in>{''2:prolog_data_2b'',''2:prolog_data_2d'',
   ''2:prolog_data_2a'',''2:prolog_data_2f''})"

lemma lpp_machine_decode_integer[simp]:
 "lpp_machine_decode (lpp_integer_value n)=Some (LPPMachineInteger n)"
 using lpp_machine_decode_value[of "LPPMachineInteger n"] by simp
lemma lpp_machine_decode_float[simp]:
 "lpp_binary64_finite bits \<Longrightarrow>
  lpp_machine_decode (lpp_binary64_value bits)=Some (LPPMachineFloat bits)"
 using lpp_machine_decode_value[of "LPPMachineFloat bits"] by simp

lemma lpp_machine_binary_profile:
 assumes a: "lpp_machine_valid a" and b: "lpp_machine_valid b"
   and name: "lpp_machine_binary_name f"
 shows "lpp_binary64_profile_operation fallback (LPCUser f)
   [lpp_machine_value a,lpp_machine_value b] =
   map_option lpp_machine_value (lpp_machine_binary f a b)"
 using a b name
 by (cases a; cases b)
   (auto simp: lpp_binary64_profile_operation_def lpp_binary64_fallback_def
     lpp_machine_binary_name_def lpp_machine_decode_value
     lpp_stable_decode_integer_literal lpp_stable_decode_binary64
     split: if_splits)

datatype lpp_machine_expression = LPPMachineLiteral lpp_machine_scalar |
 LPPMachineBinary string lpp_machine_expression lpp_machine_expression

fun lpp_machine_term where
 "lpp_machine_term (LPPMachineInteger n) = lpp_integer_term n"
| "lpp_machine_term (LPPMachineFloat b) = Fun (LPCUser (lpp_binary64_name b)) []"
fun lpp_machine_expression_term where
 "lpp_machine_expression_term (LPPMachineLiteral a)=lpp_machine_term a"
| "lpp_machine_expression_term (LPPMachineBinary f a b)=
    Fun (LPCUser f) [lpp_machine_expression_term a,lpp_machine_expression_term b]"
fun lpp_machine_evaluate where
 "lpp_machine_evaluate (LPPMachineLiteral a)=(if lpp_machine_valid a then Some a else None)"
| "lpp_machine_evaluate (LPPMachineBinary f a b)=
   (if lpp_machine_binary_name f then
     (case (lpp_machine_evaluate a,lpp_machine_evaluate b) of (Some x,Some y) \<Rightarrow>
       lpp_machine_binary f x y | _ \<Rightarrow> None)
    else None)"

lemma lpp_machine_term_eval:
 "lp_ieval (lpp_machine_term a) eta=lpp_machine_value a"
 by (cases a) (simp_all add: lpp_integer_term_def lpp_integer_value_def lpp_binary64_value_def)

lemma lpp_machine_evaluate_valid:
 "lpp_machine_evaluate e=Some v \<Longrightarrow> lpp_machine_valid v"
 by (cases e) (auto split: if_splits option.splits prod.splits dest: lpp_machine_binary_valid)

lemma lpp_machine_evaluation_sound:
 assumes "lpp_machine_evaluate e=Some v"
 shows "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
   (lp_ieval (lpp_machine_expression_term e) eta) (lpp_machine_value v)"
 using assms
proof (induct e arbitrary: v)
 case (LPPMachineLiteral a)
 then have valid: "lpp_machine_valid a" and v: "v=a" by (auto split: if_splits)
 show ?case unfolding v
   by (simp only: lpp_machine_expression_term.simps lpp_machine_term_eval;
       rule lpp_stable_scalar_evaluation.scalar[OF lpp_machine_scalar_fraction[OF valid]])
next
 case (LPPMachineBinary f a b)
 obtain x y where left: "lpp_machine_evaluate a=Some x" and right: "lpp_machine_evaluate b=Some y"
   and result: "lpp_machine_binary f x y=Some v" and name: "lpp_machine_binary_name f"
   using LPPMachineBinary.prems by (auto split: if_splits option.splits prod.splits)
 have operated: "lpp_binary64_profile_operation fallback (LPCUser f)
   [lpp_machine_value x,lpp_machine_value y]=Some (lpp_machine_value v)"
   using lpp_machine_binary_profile[OF lpp_machine_evaluate_valid[OF left]
     lpp_machine_evaluate_valid[OF right] name] result by simp
 have scalar: "lpp_scalar_fraction (lpp_machine_value v)
     (fst (lpp_machine_fraction v)) (snd (lpp_machine_fraction v))"
   by (rule lpp_machine_scalar_fraction[OF lpp_machine_binary_valid[OF result]])
 show ?case
   by (simp only: lpp_machine_expression_term.simps lp_ieval.simps list.map;
       rule lpp_stable_scalar_evaluation.binary[OF LPPMachineBinary.hyps(1)[OF left]
         LPPMachineBinary.hyps(2)[OF right] operated scalar])
qed

ML \<open>
val checked = [@{thm lpp_machine_binary_profile}, @{thm lpp_machine_evaluation_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted binary64 evaluation dependency" else ();
\<close>
end
