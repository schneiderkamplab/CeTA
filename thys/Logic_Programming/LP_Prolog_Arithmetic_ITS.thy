theory LP_Prolog_Arithmetic_ITS
  imports LP_Prolog_Arithmetic ITS_Arithmetic.IA4_Normalization
begin

text \<open>This translation uses the existing ITS interpreted signature. Prolog
floor division and signed remainder are translated through a positive divisor;
using the ITS Euclidean operators directly with a negative divisor is wrong.\<close>

abbreviation lpp_ia_const where "lpp_ia_const n \<equiv> Fun (IA4_Base (IA.ConstF n)) []"
abbreviation lpp_ia_neg where
  "lpp_ia_neg e \<equiv> Fun (IA4_Base (IA.ProdF 2)) [lpp_ia_const (-1),e]"

fun lpp_expression_its :: "'v lpp_integer_expression \<Rightarrow> 'v ia4_exp" where
  "lpp_expression_its (LPPEConstant n) = lpp_ia_const n"
| "lpp_expression_its (LPPEVariable x) = Var (x,IA.IntT)"
| "lpp_expression_its (LPPEPositive a) = lpp_expression_its a"
| "lpp_expression_its (LPPENegate a) = lpp_ia_neg (lpp_expression_its a)"
| "lpp_expression_its (LPPEAdd a b) = Fun (IA4_Base (IA.SumF 2)) [lpp_expression_its a,lpp_expression_its b]"
| "lpp_expression_its (LPPESubtract a b) = Fun (IA4_Base (IA.SumF 2)) [lpp_expression_its a,lpp_ia_neg (lpp_expression_its b)]"
| "lpp_expression_its (LPPEMultiply a b) = Fun (IA4_Base (IA.ProdF 2)) [lpp_expression_its a,lpp_expression_its b]"
| "lpp_expression_its (LPPEDivide a d) = Fun IA4_Div
    [if d<0 then lpp_ia_neg (lpp_expression_its a) else lpp_expression_its a,lpp_ia_const (abs d)]"
| "lpp_expression_its (LPPEModulo a d) =
    (let r = Fun IA4_Mod [if d<0 then lpp_ia_neg (lpp_expression_its a) else lpp_expression_its a,lpp_ia_const (abs d)]
     in if d<0 then lpp_ia_neg r else r)"

lemma lpp_floor_quotient:
  "euclid_quot (if d<0 then -n else n) (abs d) = n div d"
  by (cases "d<0") (simp_all add: euclid_quot_def div_minus_right)

lemma lpp_signed_remainder:
  "(if d<0 then -euclid_rem (-n) (abs d) else euclid_rem n (abs d)) = n mod d"
  by (cases "d<0") (simp_all add: euclid_rem_def mod_minus_right)

theorem lpp_expression_its_value:
  "IA4.eval (lpp_expression_its e) (\<lambda>(x,ty). IA.Int (rho x)) = IA.Int (lpp_expression_value e rho)"
  by (induct e)
    (simp_all add: algebra.eval.simps euclid_quot_def euclid_rem_def div_minus_right mod_minus_right Let_def)

theorem lpp_expression_its_supported:
  "lpp_expression_check K e \<Longrightarrow> supported_exp (lpp_expression_its e)"
  by (induct e)
    (auto simp: divisor_value_def algebra.eval.simps Let_def)


theorem lpp_expression_its_type:
  "IA4.has_type (lpp_expression_its e) IA.IntT"
  by (induct e) (auto simp: Let_def less_Suc_eq)

definition lpp_check_expression_bridge where
  "lpp_check_expression_bridge K src evidence dst =
    (lpp_expression_check K evidence \<and> src=lpp_expression_term evidence \<and>
      dst=lpp_expression_its evidence)"

theorem lpp_check_expression_bridge_sound:
  assumes checked: "lpp_check_expression_bridge K src evidence dst"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lpp_integer_evaluation (lp_ieval src eta)
      (IA.to_int (IA4.eval dst (\<lambda>(x,ty). IA.Int (rho x))))"
    "IA4.has_type dst IA.IntT" "supported_exp dst"
  using lpp_expression_evaluation[of K evidence eta rho] typed
    lpp_expression_its_value[of evidence rho] lpp_expression_its_type[of evidence]
    lpp_expression_its_supported[of K evidence] checked
  by (auto simp: lpp_check_expression_bridge_def)

lemma lpp_bridge_negative_divisor_regression:
  "lpp_expression_value (LPPEDivide (LPPEConstant 7) (-3)) rho = -3"
  "lpp_expression_value (LPPEModulo (LPPEConstant 7) (-3)) rho = -2"
  "\<not> lpp_expression_check K (LPPEDivide (LPPEConstant 7) 0)"
  "\<not> lpp_expression_check [] (LPPEVariable (0::nat))"
  by simp_all

ML \<open>
val arithmetic_bridge_theorems =
  [@{thm lpp_expression_evaluation}, @{thm lpp_checked_expression_finishes},
   @{thm lpp_expression_its_value}, @{thm lpp_expression_its_type},
   @{thm lpp_expression_its_supported}] @ @{thms lpp_check_expression_bridge_sound};
val arithmetic_bridge_oracles = map (fst o fst) o Thm_Deps.all_oracles;
val arithmetic_bridge_inherited = arithmetic_bridge_oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof arithmetic_bridge_theorems orelse
  exists (fn n => not (member (op =) arithmetic_bridge_inherited n))
    (arithmetic_bridge_oracles arithmetic_bridge_theorems)
  then error "Untrusted arithmetic bridge dependency" else ();
\<close>

text \<open>The expression theorem is only a component of the source bridge.
It does not certify source control flow, helper returns, or a root verdict.\<close>
end
