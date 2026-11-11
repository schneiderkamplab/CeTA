theory LP_Prolog_Binary64_Rounding
  imports LP_Prolog_Binary64_Encoding "HOL-Library.Discrete_Functions"
begin

text \<open>Round an exact rational at the binary64 precision before encoding its
bits. Operands are converted separately before a mixed arithmetic operation;
rounding the final rational alone must not bypass operand conversion. The
boolean parameter supplies the sign of an exact zero (including signed-zero
arithmetic). No host floating-point operation is used by these definitions.\<close>

definition lpp_round_even_div :: "int \<Rightarrow> int \<Rightarrow> int" where
 "lpp_round_even_div n d =
   (let q=n div d; r=n mod d
    in if 2*r<d \<or> (2*r=d \<and> even q) then q else q+1)"

lemma lpp_round_even_div_exact:
 "0<d \<Longrightarrow> lpp_round_even_div (k*d) d=k"
 by (simp add: lpp_round_even_div_def)

lemma lpp_round_even_div_nearest:
 assumes positive: "0<d"
 shows "abs (n - d * (lpp_round_even_div n d)) \<le> abs (n - d * k)"
proof -
 let ?q="n div d" let ?r="n mod d"
 have r0: "0\<le>?r" and rd: "?r<d" using positive by simp_all
 have decompose: "n=d * ?q+?r" by (simp add: div_mult_mod_eq mult.commute)
 have lower: "abs (n - d * (lpp_round_even_div n d))\<le>?r"
   unfolding lpp_round_even_div_def Let_def
   using r0 rd decompose by (auto simp: abs_if algebra_simps split: if_splits; linarith)
 have upper: "abs (n - d * (lpp_round_even_div n d))\<le>d-?r"
   unfolding lpp_round_even_div_def Let_def
   using r0 rd decompose by (auto simp: abs_if algebra_simps split: if_splits; linarith)
 show ?thesis
 proof (cases "k\<le>?q")
  case True
  have "d * k\<le>d * ?q" by (rule mult_left_mono[OF True]) (use positive in simp)
  then show ?thesis using lower r0 decompose by (simp add: abs_if; linarith)
 next
  case False
  have "?q+1\<le>k" using False by linarith
  then have "d * (?q + 1)\<le>d * k" by (rule mult_left_mono) (use positive in simp)
  then show ?thesis using upper rd decompose by (auto simp: abs_if algebra_simps; linarith)
 qed
qed

lemma lpp_round_even_div_tie:
 assumes "0<d" "2*(n mod d)=d"
 shows "even (lpp_round_even_div n d)"
 using assms by (auto simp: lpp_round_even_div_def Let_def)

definition lpp_binary64_round_fraction :: "bool \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat option" where
 "lpp_binary64_round_fraction negative_zero numerator denominator =
  (if denominator=0 then None else
   let negative=(if numerator=0 then negative_zero else (numerator<0)\<noteq>(denominator<0));
       sign=(if negative then (2::nat)^63 else 0);
       n=abs numerator; d=abs denominator;
       estimate=int (floor_log (nat n))-int (floor_log (nat d));
       below=(if 0\<le>estimate then n<d*2^(nat estimate) else n*2^(nat (-estimate))<d);
       exponent=estimate-(if below then 1 else 0);
       power=max (exponent-52) (-1074);
       scaled_n=n*2^(nat (-power)); scaled_d=d*2^(nat power);
       q=nat (lpp_round_even_div scaled_n scaled_d);
       carry=(q=(2::nat)^53);
       encoded_exponent=nat (power+1075+(if carry then 1 else 0));
       fraction=(if carry then 0 else q-2^52)
   in if numerator=0 \<or> exponent< -1075 then Some sign
      else if 1023<exponent \<or> 2^53<q then None
      else if q<2^52 then Some (sign+q)
      else if encoded_exponent<2047 then Some (sign+encoded_exponent*2^52+fraction)
      else None)"

lemma lpp_binary64_round_zero:
 "lpp_binary64_round_fraction False 0 1=Some 0"
 "lpp_binary64_round_fraction True 0 1=Some (2^63)"
 by (simp_all add: lpp_binary64_round_fraction_def Let_def)

lemma lpp_binary64_round_unit:
 "lpp_binary64_round_fraction False 1 1=Some 4607182418800017408"
 "lpp_binary64_round_fraction False (-1) 1=Some 13830554455654793216"
 by (simp_all add: lpp_binary64_round_fraction_def lpp_round_even_div_def Let_def)

ML \<open>
val checked = [@{thm lpp_round_even_div_nearest}, @{thm lpp_round_even_div_tie},
 @{thm lpp_round_even_div_exact}, @{thm lpp_binary64_round_zero(1)}, @{thm lpp_binary64_round_unit(1)}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted binary64 rounding dependency" else ();
\<close>
end
