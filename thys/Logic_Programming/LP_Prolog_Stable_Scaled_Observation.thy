theory LP_Prolog_Stable_Scaled_Observation
 imports LP_Prolog_Stable_Bound_Projection
begin

text \<open>All finite binary64 values and integers embed exactly into integers
at the common scale 2^1074. This observes successful evaluated scalars; it does
not round source arithmetic or assert that an arbitrary ground term evaluates.
Existing floor coordinates retain their meaning.\<close>

definition lpp_scalar_scale :: int where "lpp_scalar_scale = 2^1074"

lemma lpp_scalar_scale_positive: "0 < lpp_scalar_scale"
  by (simp add: lpp_scalar_scale_def)

lemma lpp_binary64_denominator_divides_scale:
  "snd (lpp_binary64_fraction bits) dvd lpp_scalar_scale"
proof -
  let ?e = "(bits div 2^52) mod 2048"
  have exponent: "nat (- (if ?e=0 then -1074 else int ?e-1075)) \<le> 1074"
    by auto
  show ?thesis unfolding lpp_binary64_fraction_def lpp_scalar_scale_def Let_def
    by (simp only: snd_conv; rule le_imp_power_dvd[OF exponent])
qed

lemma lpp_scalar_denominator_divides_scale:
  "lpp_scalar_fraction t n d \<Longrightarrow> d dvd lpp_scalar_scale"
  using lpp_binary64_denominator_divides_scale
  by (auto simp: lpp_scalar_fraction_def; metis snd_conv)

definition lpp_scalar_scaled where
  "lpp_scalar_scaled t = (THE k. \<exists>n d. lpp_scalar_fraction t n d \<and>
    k=(n*lpp_scalar_scale) div d)"

lemma lpp_scalar_scaled_exact:
  assumes observed: "lpp_scalar_fraction t n d"
  shows "lpp_scalar_scaled t=(n*lpp_scalar_scale) div d"
  unfolding lpp_scalar_scaled_def
proof (rule the_equality)
  show "\<exists>a b. lpp_scalar_fraction t a b \<and>
      (n*lpp_scalar_scale) div d=(a*lpp_scalar_scale) div b" using observed by blast
  fix k assume "\<exists>a b. lpp_scalar_fraction t a b \<and> k=(a*lpp_scalar_scale) div b"
  then show "k=(n*lpp_scalar_scale) div d"
    using lpp_scalar_fraction_unique[OF observed] by blast
qed

definition lpp_stable_scaled_bound where
  "lpp_stable_scaled_bound operation expression =
    (if \<exists>v. lpp_stable_scalar_evaluation operation expression v
     then lpp_scalar_scaled (THE v. lpp_stable_scalar_evaluation operation expression v)
     else 0)"

lemma lpp_stable_scaled_bound_exact:
  assumes evaluated: "lpp_stable_scalar_evaluation operation expression v"
  shows "lpp_stable_scaled_bound operation expression=lpp_scalar_scaled v"
proof -
  have unique: "(THE w. lpp_stable_scalar_evaluation operation expression w)=v"
    by (rule the_equality[where P="lpp_stable_scalar_evaluation operation expression", OF evaluated])
      (use evaluated in \<open>auto dest: lpp_stable_scalar_evaluation_unique\<close>)
  show ?thesis using evaluated unique by (auto simp: lpp_stable_scaled_bound_def)
qed

lemma lpp_scaled_fraction_order:
  fixes n m d e q :: int
  assumes d: "0<d" and e: "0<e" and q: "0<q"
    and dq: "d dvd q" and eq: "e dvd q"
  shows "lpp_integer_compare c ((n*q) div d) ((m*q) div e) =
    lpp_integer_compare c (n*e) (m*d)"
proof -
  have nd: "d dvd n*q" using dq by simp
  have me: "e dvd m*q" using eq by simp
  have left: "((n*q) div d)*(d*e)=(n*e)*q"
    using dvd_div_mult_self[OF nd] by (simp add: algebra_simps)
  have right: "((m*q) div e)*(d*e)=(m*d)*q"
    using dvd_div_mult_self[OF me] by (simp add: algebra_simps)
  have positive: "0<d*e" using d e by simp
  have less: "((n*q) div d < (m*q) div e) = (n*e < m*d)"
    using mult_less_cancel_right_pos[OF positive, of "(n*q) div d" "(m*q) div e"]
      mult_less_cancel_right_pos[OF q, of "n*e" "m*d"] left right by metis
  have leq: "((n*q) div d \<le> (m*q) div e) = (n*e \<le> m*d)"
    using mult_le_cancel_right_pos[OF positive, of "(n*q) div d" "(m*q) div e"]
      mult_le_cancel_right_pos[OF q, of "n*e" "m*d"] left right by metis
  have equal: "((n*q) div d = (m*q) div e) = (n*e = m*d)"
    using less leq by linarith
  show ?thesis using less leq equal by (cases c) auto
qed

lemma lpp_stable_scaled_comparison:
  assumes observed: "lpp_stable_compare_outcome operation c a b (LPPBuiltinSuccess LPIVar)"
  shows "lpp_integer_compare c (lpp_stable_scaled_bound operation a)
    (lpp_stable_scaled_bound operation b)"
proof -
  obtain v w n d m e where left: "lpp_stable_scalar_evaluation operation a v"
    and right: "lpp_stable_scalar_evaluation operation b w"
    and lv: "lpp_scalar_fraction v n d" and rv: "lpp_scalar_fraction w m e"
    and truth: "lpp_integer_compare c (n*e) (m*d)"
    using observed by (auto simp: lpp_stable_compare_outcome_def lpp_stable_compare_values_def split: if_splits)
  have exact: "lpp_integer_compare c ((n*lpp_scalar_scale) div d) ((m*lpp_scalar_scale) div e)"
    using lpp_scaled_fraction_order[OF lpp_scalar_fraction_denominator[OF lv]
      lpp_scalar_fraction_denominator[OF rv] lpp_scalar_scale_positive
      lpp_scalar_denominator_divides_scale[OF lv] lpp_scalar_denominator_divides_scale[OF rv]] truth by simp
  show ?thesis using exact by (simp add: lpp_stable_scaled_bound_exact[OF left]
    lpp_stable_scaled_bound_exact[OF right] lpp_scalar_scaled_exact[OF lv] lpp_scalar_scaled_exact[OF rv])
qed

ML \<open>
val checked = [@{thm lpp_scalar_denominator_divides_scale}, @{thm lpp_scalar_scaled_exact},
  @{thm lpp_stable_scaled_bound_exact}, @{thm lpp_stable_scaled_comparison}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted exact scalar observation dependency" else ();
\<close>
end
