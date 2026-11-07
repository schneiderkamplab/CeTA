theory LP_Prolog_Stable_Return_Constraints
 imports LP_Prolog_Success_Magnitude_Program LP_Prolog_Stable_Magnitude_Quotient_Descent
begin

text \<open>Return bounds refer to an actual successful prefix call, with its
output selected by the complete checked success program. They do not follow
from helper termination. The quotient facts hold also when evaluation fails,
using the established scalar observation's default value.\<close>

datatype 'v lpp_return_constraint =
    LPPReturnNonnegative "(string lp_cut_symbol,'v) term"
  | LPPReturnConstant int
  | LPPReturnQuotient "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPReturnStrictQuotient "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPReturnHelper nat nat

fun lpp_check_return_constraint where
  "lpp_check_return_constraint summaries ps (LPPReturnHelper i j) =
    (i<length ps \<and> j<length (snd (ps!i)) \<and>
      j\<in>set (summaries (fst (ps!i),length (snd (ps!i)))))"
| "lpp_check_return_constraint summaries ps _ = True"

fun lpp_return_constraint_holds where
  "lpp_return_constraint_holds operation eta ps (LPPReturnNonnegative t) =
    (0\<le>abs (lpp_stable_scaled_bound operation (lp_ieval t eta)))"
| "lpp_return_constraint_holds operation eta ps (LPPReturnConstant n) =
    (abs (lpp_stable_scaled_bound operation (lp_ieval (lpp_integer_term n) eta))=abs n*lpp_scalar_scale)"
| "lpp_return_constraint_holds operation eta ps (LPPReturnQuotient a b) =
    (abs (lpp_stable_scaled_bound operation (lp_ieval (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]) eta))\<le>
      abs (lpp_stable_scaled_bound operation (lp_ieval a eta)))"
| "lpp_return_constraint_holds operation eta ps (LPPReturnStrictQuotient a b) =
    (abs (lpp_stable_scaled_bound operation (lp_ieval b eta))\<le>lpp_scalar_scale \<or>
     abs (lpp_stable_scaled_bound operation (lp_ieval a eta))\<le>0 \<or>
     abs (lpp_stable_scaled_bound operation (lp_ieval (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]) eta))<
      abs (lpp_stable_scaled_bound operation (lp_ieval a eta)))"
| "lpp_return_constraint_holds operation eta ps (LPPReturnHelper i j) =
    (abs (lpp_stable_scaled_bound operation (lp_ieval (snd (ps!i)!j) eta))\<le>
      lpp_magnitude_max operation (map (\<lambda>t. lp_ieval t eta) (lpp_magnitude_inputs j (snd (ps!i)))))"

theorem lpp_check_return_constraint_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_magnitude_program summaries P receipts"
    and checked: "lpp_check_return_constraint summaries ps constraint"
    and success: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>a. lpp_success_atom_eval a eta) ps)"
  shows "lpp_return_constraint_holds operation eta ps constraint"
proof (cases constraint)
  case (LPPReturnNonnegative t) then show ?thesis by simp
next
  case (LPPReturnConstant n)
  then show ?thesis using lpp_scalar_scale_positive
    by (simp add: lpp_stable_scaled_integer[OF lpp_stable_integer_literal] abs_mult)
next
  case (LPPReturnQuotient a b)
  then show ?thesis using lpp_stable_quotient_abs_bound[OF compatible, of "lp_ieval a eta" "lp_ieval b eta"] by simp
next
  case (LPPReturnStrictQuotient a b)
  have strict: "abs (lpp_stable_scaled_bound operation (lp_ieval b eta))>lpp_scalar_scale \<Longrightarrow>
    abs (lpp_stable_scaled_bound operation (lp_ieval a eta))>0 \<Longrightarrow>
    abs (lpp_stable_scaled_bound operation (lp_ieval (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]) eta))<
    abs (lpp_stable_scaled_bound operation (lp_ieval a eta))"
    using lpp_stable_quotient_abs_strict[where operation=operation and a="lp_ieval a eta" and b="lp_ieval b eta", OF compatible] by simp
  show ?thesis unfolding LPPReturnStrictQuotient lpp_return_constraint_holds.simps
    using strict by linarith
next
  case (LPPReturnHelper i j)
  have index: "i<length ps" "j<length (snd (ps!i))"
    and selected: "j\<in>set (summaries (fst (ps!i),length (snd (ps!i))))"
    using checked by (auto simp: LPPReturnHelper)
  have actual: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (ps!i) eta)"
    using success index(1) by (simp add: list_all_length)
  have bound: "lpp_magnitude_holds operation summaries (lpp_success_atom_eval (ps!i) eta)"
    by (rule lpp_check_magnitude_program_sound[OF compatible program actual])
  have selected_bound: "abs (lpp_stable_scaled_bound operation
      (snd (lpp_success_atom_eval (ps!i) eta)!j)) \<le>
    lpp_magnitude_max operation (lpp_magnitude_inputs j (snd (lpp_success_atom_eval (ps!i) eta)))"
    using bound selected unfolding lpp_magnitude_holds_def lpp_success_atom_eval_def
    by auto
  show ?thesis using selected_bound index(2)
    by (simp add: LPPReturnHelper lpp_success_atom_eval_def lpp_magnitude_inputs_map)
qed

ML \<open>
val checked = [@{thm lpp_check_return_constraint_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted return constraint dependency" else ();
\<close>
end
