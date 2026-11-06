theory LP_Prolog_Binary64_Observation
  imports LP_Prolog_Fraction_Bounds
begin

text \<open>Exact scalar observations mirror numeric.rs Value::fraction.
They do not model floating addition or assert successful source evaluation.
A source bridge must bind the bits to the original finite scalar and retain
error branches for all other terms.\<close>

definition lpp_binary64_finite where
  "lpp_binary64_finite bits = (bits < (2::nat)^64 \<and> (bits div 2^52) mod 2048 < 2047)"

definition lpp_binary64_fraction :: "nat \<Rightarrow> int \<times> int" where
  "lpp_binary64_fraction bits =
    (let exponent=(bits div 2^52) mod 2048;
         significand=bits mod 2^52;
         mantissa=(if exponent=0 then significand else 2^52+significand);
         power=(if exponent=0 then -1074 else int exponent-1075);
         polarity=(if bits div 2^63=0 then 1 else -1)
     in (polarity*int mantissa*2^(nat power),2^(nat (-power))))"

definition lpp_binary64_floor where
  "lpp_binary64_floor bits = fst (lpp_binary64_fraction bits) div snd (lpp_binary64_fraction bits)"
definition lpp_binary64_strict_floor where
  "lpp_binary64_strict_floor bits = (fst (lpp_binary64_fraction bits)-1) div snd (lpp_binary64_fraction bits)"

lemma lpp_binary64_denominator_positive:
  "0 < snd (lpp_binary64_fraction bits)"
  by (simp add: lpp_binary64_fraction_def Let_def)

lemma lpp_binary64_integer_upper_bound:
  "k * snd (lpp_binary64_fraction bits)\<le>fst (lpp_binary64_fraction bits)
    \<longleftrightarrow> k\<le>lpp_binary64_floor bits"
  unfolding lpp_binary64_floor_def
  by (rule lpp_fraction_floor_bound[OF lpp_binary64_denominator_positive])

lemma lpp_binary64_integer_strict_upper_bound:
  "k * snd (lpp_binary64_fraction bits) < fst (lpp_binary64_fraction bits)
    \<longleftrightarrow> k\<le>lpp_binary64_strict_floor bits"
  unfolding lpp_binary64_strict_floor_def
  by (rule lpp_fraction_strict_bound[OF lpp_binary64_denominator_positive])

lemma lpp_binary64_counter_descent:
  assumes bound: "k * snd (lpp_binary64_fraction bits)\<le>fst (lpp_binary64_fraction bits)"
    and progress: "k<later"
  shows "nat (lpp_binary64_floor bits-later+1)<nat (lpp_binary64_floor bits-k+1)"
  unfolding lpp_binary64_floor_def
  by (rule lpp_fraction_bounded_counter_descent[OF lpp_binary64_denominator_positive bound progress])

ML \<open>
val checked = [@{thm lpp_binary64_denominator_positive},
  @{thm lpp_binary64_integer_upper_bound}, @{thm lpp_binary64_integer_strict_upper_bound},
  @{thm lpp_binary64_counter_descent}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted binary64 observation dependency" else ();
\<close>
end
