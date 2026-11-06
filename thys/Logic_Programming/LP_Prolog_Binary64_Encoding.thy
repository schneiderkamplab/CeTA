theory LP_Prolog_Binary64_Encoding
  imports LP_Prolog_Binary64_Observation
begin

fun lpp_fixed_hex_digits :: "nat \<Rightarrow> nat \<Rightarrow> string" where
  "lpp_fixed_hex_digits 0 bits = []"
| "lpp_fixed_hex_digits (Suc width) bits =
    lpp_fixed_hex_digits width (bits div 16) @ [''0123456789abcdef'' ! (bits mod 16)]"

lemma lpp_fixed_hex_digits_injective:
  assumes a: "a<16^width" and b: "b<16^width"
    and equal: "lpp_fixed_hex_digits width a=lpp_fixed_hex_digits width b"
  shows "a=b"
  using a b equal
proof (induct width arbitrary: a b)
  case 0 then show ?case by simp
next
  case (Suc width)
  have high: "lpp_fixed_hex_digits width (a div 16)=lpp_fixed_hex_digits width (b div 16)"
    and low: "''0123456789abcdef'' ! (a mod 16) = ''0123456789abcdef'' ! (b mod 16)"
    using Suc.prems(3) by simp_all
  have ab: "a div 16<16^width" "b div 16<16^width"
    using Suc.prems(1,2) by (simp_all add: div_less_iff_less_mult power_Suc mult.commute)
  have quotient: "a div 16=b div 16" by (rule Suc.hyps[OF ab high])
  have remainder: "a mod 16=b mod 16"
    using lpp_hex_index_injective[of "a mod 16" "b mod 16"] low by simp
  show ?case using quotient remainder div_mult_mod_eq[of a 16] div_mult_mod_eq[of b 16] by arith
qed

definition lpp_binary64_name where
  "lpp_binary64_name bits = ''0:prolog_data_'' @ concat (map lpp_hex_char
    (char_of_nat 0 # (''prolog.float:'' @ lpp_fixed_hex_digits 16 bits)))"
definition lpp_binary64_value where
  "lpp_binary64_value bits = LPIFun (LPCUser (lpp_binary64_name bits)) []"

lemma lpp_binary64_name_injective:
  assumes a: "a<(2::nat)^64" and b: "b<(2::nat)^64"
    and names: "lpp_binary64_name a=lpp_binary64_name b"
  shows "a=b"
proof -
  have encoded: "concat (map lpp_hex_char (char_of_nat 0 # (''prolog.float:'' @ lpp_fixed_hex_digits 16 a))) =
    concat (map lpp_hex_char (char_of_nat 0 # (''prolog.float:'' @ lpp_fixed_hex_digits 16 b)))"
    using names by (simp add: lpp_binary64_name_def)
  have digits: "lpp_fixed_hex_digits 16 a=lpp_fixed_hex_digits 16 b"
    using lpp_hex_string_injective[OF encoded] by simp
  show ?thesis by (rule lpp_fixed_hex_digits_injective[OF _ _ digits]) (use a b in simp_all)
qed

lemma lpp_binary64_value_injective:
  "a<(2::nat)^64 \<Longrightarrow> b<(2::nat)^64 \<Longrightarrow>
    lpp_binary64_value a=lpp_binary64_value b \<Longrightarrow> a=b"
  by (auto simp: lpp_binary64_value_def intro: lpp_binary64_name_injective)

lemma lpp_binary64_value_ground:
  "lp_seg_ground (lpp_binary64_value bits)"
  by (simp add: lpp_binary64_value_def lp_seg_ground.intros)

lemma lpp_binary64_value_subst[simp]:
  "lp_isubst (lpp_binary64_value bits) sigma=lpp_binary64_value bits"
  by (simp add: lpp_binary64_value_def)

lemma lpp_binary64_not_integer:
  "lpp_binary64_value bits\<noteq>lpp_integer_value n"
proof
  assume same: "lpp_binary64_value bits=lpp_integer_value n"
  have encoded: "concat (map lpp_hex_char (char_of_nat 0 # (''prolog.float:'' @ lpp_fixed_hex_digits 16 bits))) =
    concat (map lpp_hex_char (char_of_nat 0 # (''prolog.integer:'' @ show n)))"
    using same by (simp add: lpp_binary64_value_def lpp_integer_value_def lpp_binary64_name_def lpp_integer_name_def)
  show False using lpp_hex_string_injective[OF encoded] by simp
qed

ML \<open>
val checked = [@{thm lpp_fixed_hex_digits_injective}, @{thm lpp_binary64_name_injective},
  @{thm lpp_binary64_value_injective}, @{thm lpp_binary64_value_ground},
  @{thm lpp_binary64_value_subst}, @{thm lpp_binary64_not_integer}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted binary64 encoding dependency" else ();
\<close>
end
