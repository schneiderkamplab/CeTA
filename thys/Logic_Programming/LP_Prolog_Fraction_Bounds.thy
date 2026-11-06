theory LP_Prolog_Fraction_Bounds
  imports LP_Prolog_Arithmetic_Semantics
begin

text \<open>The native numeric comparison uses exact numerator/denominator
cross multiplication, including for binary64 operands. These integer bounds
observe a fixed rational value; they do not assert that the source operand is
an integer or replace floating arithmetic with integer arithmetic. Binding the
fraction to the source scalar and transporting that binding remain separate
source-proof obligations.\<close>

lemma lpp_fraction_floor_bound:
  fixes n d k :: int
  assumes positive: "0<d"
  shows "k*d\<le>n \<longleftrightarrow> k\<le>n div d"
proof -
  have remainder: "0\<le>n mod d" "n mod d<d"
    using positive by simp_all
  have decomposition: "n div d*d+n mod d=n"
    by simp
  show ?thesis
  proof (cases "k\<le>n div d")
    case True
    have "k*d\<le>n div d*d" by (rule mult_right_mono[OF True]) (use positive in simp)
    then show ?thesis using True remainder decomposition by linarith
  next
    case False
    then have step: "n div d+1\<le>k" by simp
    have "(n div d+1)*d\<le>k*d" by (rule mult_right_mono[OF step]) (use positive in simp)
    then have "n div d*d+d\<le>k*d" by (simp add: algebra_simps)
    then have "n<k*d" using remainder decomposition by linarith
    then show ?thesis using False by simp
  qed
qed

lemma lpp_fraction_strict_bound:
  fixes n d k :: int
  assumes "0<d"
  shows "k*d<n \<longleftrightarrow> k\<le>(n-1) div d"
  using lpp_fraction_floor_bound[where k=k and n="n-1", OF assms] by simp

lemma lpp_fraction_ceiling_bound:
  fixes n d k :: int
  assumes "0<d"
  shows "n\<le>k*d \<longleftrightarrow> -((-n) div d)\<le>k"
  using lpp_fraction_floor_bound[where k="-k" and n="-n", OF assms] by (simp only: mult_minus_left; linarith)

lemma lpp_fraction_bounded_counter_descent:
  fixes n d k later :: int
  assumes denominator: "0<d" and bounded: "k*d\<le>n" and progress: "k<later"
  shows "nat (n div d-later+1)<nat (n div d-k+1)"
  using lpp_fraction_floor_bound[where k=k and n=n, OF denominator] bounded progress by simp

ML \<open>
val checked = [@{thm lpp_fraction_floor_bound}, @{thm lpp_fraction_strict_bound},
  @{thm lpp_fraction_ceiling_bound}, @{thm lpp_fraction_bounded_counter_descent}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted fraction bound dependency" else ();
\<close>
end
