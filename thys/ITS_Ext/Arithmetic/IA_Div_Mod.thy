theory IA_Div_Mod
  imports LTS.IA_Instance
begin

definition euclid_quot :: "int \<Rightarrow> int \<Rightarrow> int" where
  "euclid_quot n d = (if d < 0 then - (n div (-d)) else n div d)"
definition euclid_rem :: "int \<Rightarrow> int \<Rightarrow> int" where
  "euclid_rem n d = n mod abs d"

lemma euclid_quot_rem:
  assumes "d \<noteq> 0"
  shows "n = d * euclid_quot n d + euclid_rem n d"
    "0 \<le> euclid_rem n d" "euclid_rem n d < abs d"
proof -
  show "n = d * euclid_quot n d + euclid_rem n d"
  proof (cases "d < 0")
    case True
    have "n = (-d) * (n div (-d)) + n mod (-d)"
      using div_mult_mod_eq[of n "-d"] by (simp add: mult.commute)
    with True show ?thesis by (simp add: euclid_quot_def euclid_rem_def)
  next
    case False
    have "n = d * (n div d) + n mod d"
      using div_mult_mod_eq[of n d] by (simp add: mult.commute)
    with False show ?thesis by (simp add: euclid_quot_def euclid_rem_def)
  qed
  show "0 \<le> euclid_rem n d" "euclid_rem n d < abs d"
    using assms by (auto simp: euclid_rem_def)
qed

lemma euclid_quot_rem_unique:
  assumes "d \<noteq> 0" "n = d*q+r" "0 \<le> r" "r < abs d"
  shows "q = euclid_quot n d \<and> r = euclid_rem n d"
proof (cases "d < 0")
  case True
  have eq: "n = (-d) * (-q) + r" using assms(2) by simp
  from int_div_pos_eq[OF eq assms(3)] int_mod_pos_eq[OF eq assms(3)] assms True
  show ?thesis by (auto simp: euclid_quot_def euclid_rem_def)
next
  case False
  from int_div_pos_eq[OF assms(2-3)] int_mod_pos_eq[OF assms(2-3)] assms False
  show ?thesis by (auto simp: euclid_quot_def euclid_rem_def)
qed

lemma euclid_ex_unique:
  fixes n d :: int
  assumes "d \<noteq> 0"
  shows "\<exists>!qr. n = d * fst qr + snd qr \<and> 0 \<le> snd qr \<and> snd qr < abs d"
proof (rule ex1I[of _ "(euclid_quot n d,euclid_rem n d)"])
  show "n = d * fst (euclid_quot n d,euclid_rem n d) + snd (euclid_quot n d,euclid_rem n d) \<and>
    0 \<le> snd (euclid_quot n d,euclid_rem n d) \<and> snd (euclid_quot n d,euclid_rem n d) < abs d"
    using euclid_quot_rem[OF assms, of n] by simp
  fix qr
  assume h: "n = d * fst qr + snd qr \<and> 0 \<le> snd qr \<and> snd qr < abs d"
  from euclid_quot_rem_unique[OF assms, of n "fst qr" "snd qr"] h
  show "qr = (euclid_quot n d,euclid_rem n d)" by (cases qr, simp)
qed

text \<open>A separate interpreted signature extends the established integer
 arithmetic without weakening its polynomial normalization theorems. CPF keeps
 binary div/mod syntax; the parser will reject nonconstant and zero divisors.\<close>

datatype ia4_sig = IA4_Base IA.sig | IA4_Div | IA4_Mod

derive compare_order IA.sig IA.ty ia4_sig

instantiation ia4_sig :: showl
begin
fun showsl_ia4_sig where
  "showsl_ia4_sig (IA4_Base f) = showsl f"
| "showsl_ia4_sig IA4_Div = showsl_lit (STR ''div'')"
| "showsl_ia4_sig IA4_Mod = showsl_lit (STR ''mod'')"
definition "showsl_list (xs :: ia4_sig list) = default_showsl_list showsl xs"
instance ..
end

locale IA4_locale
begin
fun type_of_fun where
  "type_of_fun (IA4_Base f) = IA.type_of_fun f"
| "type_of_fun IA4_Div = ([IA.IntT,IA.IntT],IA.IntT)"
| "type_of_fun IA4_Mod = ([IA.IntT,IA.IntT],IA.IntT)"
fun I where
  "I (IA4_Base f) xs = IA.I f xs"
| "I IA4_Div [a,d] = IA.Int (euclid_quot (IA.to_int a) (IA.to_int d))"
| "I IA4_Mod [a,d] = IA.Int (euclid_rem (IA.to_int a) (IA.to_int d))"
| "I _ _ = undefined"

sublocale prelogic where I=I and type_of_fun=type_of_fun
  and Values_of_type=IA.Values_of_type and Bool_types="{IA.BoolT}"
  and to_bool=IA.to_bool and type_fixer="TYPE(_)" .

sublocale logic where I=I and type_of_fun=type_of_fun
  and Values_of_type=IA.Values_of_type and Bool_types="{IA.BoolT}"
  and to_bool=IA.to_bool and type_fixer="TYPE(_)"
proof
  fix f ds
  assume len: "length ds = length (param_types f)"
    and typed: "\<And>i. i < length ds \<Longrightarrow> ds ! i \<in> IA.Values_of_type (param_types f ! i)"
  show "I f ds \<in> IA.Values_of_type (return_type f)"
  proof (cases f)
    case (IA4_Base g)
    then show ?thesis using len typed IA.well_typed by auto
  next
    case IA4_Div
    with len obtain a d where "ds = [a,d]" by (cases ds rule: list_3_cases, auto)
    with IA4_Div show ?thesis by auto
  next
    case IA4_Mod
    with len obtain a d where "ds = [a,d]" by (cases ds rule: list_3_cases, auto)
    with IA4_Mod show ?thesis by auto
  qed
next
  fix ty :: IA.ty
  show "IA.Values_of_type ty \<noteq> {}" by (cases ty, auto)
qed
end

global_interpretation IA4: IA4_locale.
end
