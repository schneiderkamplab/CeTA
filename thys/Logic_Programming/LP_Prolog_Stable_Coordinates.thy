theory LP_Prolog_Stable_Coordinates
 imports LP_Prolog_Stable_Bound_Projection LP_Prolog_Numeric_Calls
begin

text \<open>Bound coordinates observe a fixed ground arithmetic expression.
They do not assert that its source term is an integer. Groundness is required
at the representation boundary so later substitutions cannot change a bound.
The arbitrary default for a non-evaluable ground term licenses no comparison.\<close>

datatype lpp_stable_coordinate = LPPStableInteger | LPPStableUpperBound

fun lpp_stable_coordinate_value where
  "lpp_stable_coordinate_value operation LPPStableInteger t k = (t=lpp_integer_value k)"
| "lpp_stable_coordinate_value operation LPPStableUpperBound t k =
    (lp_seg_ground t \<and> k=lpp_stable_expression_bound operation t)"

lemma lpp_stable_coordinate_subst:
  "lpp_stable_coordinate_value operation mode t k \<Longrightarrow>
    lpp_stable_coordinate_value operation mode (lp_isubst t sigma) k"
  by (cases mode) (auto simp: lp_seg_ground_subst)

lemma lpp_stable_coordinate_unique:
  "lpp_stable_coordinate_value operation mode t k \<Longrightarrow>
   lpp_stable_coordinate_value operation mode t j \<Longrightarrow> k=j"
  by (cases mode) auto

definition lpp_stable_numeric_tuple where
  "lpp_stable_numeric_tuple operation names modes ts rho =
    (length names=length ts \<and> length modes=length ts \<and>
      (\<forall>i<length names. lpp_stable_coordinate_value operation (modes!i) (ts!i) (rho (names!i))))"

lemma lpp_stable_numeric_tuple_subst:
  "lpp_stable_numeric_tuple operation names modes ts rho \<Longrightarrow>
    lpp_stable_numeric_tuple operation names modes (map (\<lambda>t. lp_isubst t sigma) ts) rho"
  by (auto simp: lpp_stable_numeric_tuple_def intro: lpp_stable_coordinate_subst)

definition lpp_stable_numeric_call where
  "lpp_stable_numeric_call operation coordinates modes a rho =
    lpp_stable_numeric_tuple operation (coordinates (fst a)) (modes (fst a)) (snd a) rho"

lemma lpp_stable_numeric_call_match:
  assumes matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and represented: "lpp_stable_numeric_call operation coordinates modes a pre"
  shows "lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval h eta) pre"
  using lpp_stable_numeric_tuple_subst[OF represented[unfolded lpp_stable_numeric_call_def], of sigma]
    matching unfolding lpp_stable_numeric_call_def lpp_success_iatom_subst_def
    by (metis fst_conv snd_conv)

lemma lpp_stable_coordinate_comparison:
  assumes compatible: "lpp_stable_integer_operations operation"
    and counter: "lpp_stable_coordinate_value operation LPPStableInteger a k"
    and bound: "lpp_stable_coordinate_value operation LPPStableUpperBound b j"
    and ordered: "c=LPPIntLess \<or> c=LPPIntLessEqual"
    and success: "lpp_stable_compare_outcome operation c a b (LPPBuiltinSuccess LPIVar)"
  shows "k\<le>j"
proof -
  have integer: "lpp_integer_evaluation a k"
    using counter by (auto intro: lpp_integer_evaluation.intros)
  show ?thesis using lpp_stable_expression_bound_comparison[OF compatible integer ordered success] bound by simp
qed

ML \<open>
val checked = [@{thm lpp_stable_coordinate_subst}, @{thm lpp_stable_coordinate_unique},
  @{thm lpp_stable_numeric_tuple_subst}, @{thm lpp_stable_numeric_call_match},
  @{thm lpp_stable_coordinate_comparison}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable coordinate dependency" else ();
\<close>
end
