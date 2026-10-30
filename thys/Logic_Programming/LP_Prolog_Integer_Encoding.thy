theory LP_Prolog_Integer_Encoding
  imports LP_Prolog_Integer_NO Show.Number_Parser
begin

lemma lpp_hex_index_injective:
  assumes "i<16" "j<16"
  shows "(''0123456789abcdef''!i = ''0123456789abcdef''!j) = (i=j)"
  by (rule nth_eq_iff_index_eq) (use assms in simp_all)

lemma lpp_hex_char_injective:
  assumes "lpp_hex_char a = lpp_hex_char b"
  shows "a=b"
proof -
  have bounda: "nat_of_char a div 16 < 16" and boundb: "nat_of_char b div 16 < 16"
    by (simp_all add: nat_of_char_def div_less_iff_less_mult)
  have high: "nat_of_char a div 16 = nat_of_char b div 16"
    and low: "nat_of_char a mod 16 = nat_of_char b mod 16"
    using assms lpp_hex_index_injective[OF bounda boundb]
      lpp_hex_index_injective[of "nat_of_char a mod 16" "nat_of_char b mod 16"]
    by (auto simp: lpp_hex_char_def)
  have "nat_of_char a = nat_of_char b"
    using high low div_mult_mod_eq[of "nat_of_char a" 16]
      div_mult_mod_eq[of "nat_of_char b" 16] by arith
  then show ?thesis by (simp add: nat_of_char_def)
qed

lemma lpp_hex_string_injective:
  "concat (map lpp_hex_char xs) = concat (map lpp_hex_char ys) \<Longrightarrow> xs=ys"
proof (induct xs arbitrary: ys)
  case Nil then show ?case by (cases ys) (simp_all add: lpp_hex_char_def)
next
  case (Cons x xs)
  then obtain y zs where ys: "ys=y#zs" by (cases ys) (auto simp: lpp_hex_char_def)
  have head: "lpp_hex_char x=lpp_hex_char y" and tail:
    "concat (map lpp_hex_char xs)=concat (map lpp_hex_char zs)"
    using Cons.prems ys by (auto simp: lpp_hex_char_def[abs_def])
  show ?case using lpp_hex_char_injective[OF head] Cons.hyps[OF tail] ys by simp
qed

lemma lpp_integer_name_injective:
  assumes names: "lpp_integer_name n=lpp_integer_name m"
  shows "n=m"
proof -
  have encoded: "concat (map lpp_hex_char (char_of_nat 0 # (''prolog.integer:'' @ show n))) =
    concat (map lpp_hex_char (char_of_nat 0 # (''prolog.integer:'' @ show m)))"
    using names by (simp add: lpp_integer_name_def)
  have chars: "char_of_nat 0 # (''prolog.integer:'' @ show n) = char_of_nat 0 # (''prolog.integer:'' @ show m)"
    by (rule lpp_hex_string_injective[OF encoded])
  have printed: "show n=show m" using chars by simp
  show ?thesis using inj_show_int printed by (rule injD)
qed

lemma lpp_integer_name_eq_iff[simp]:
  "lpp_integer_name n=lpp_integer_name m \<longleftrightarrow> n=m"
  by (auto dest: lpp_integer_name_injective)

lemma lpp_integer_value_injective[simp]:
  "lpp_integer_value n=lpp_integer_value m \<longleftrightarrow> n=m"
  by (auto simp: lpp_integer_value_def dest: lpp_integer_name_injective)

end
