theory LP_Prolog_Stable_Profile_Operations
  imports LP_Prolog_Stable_Fuel_Evaluation
begin

text \<open>The integer fragment of the source profile is fixed here. Operations
outside this fragment retain one arbitrary fixed partial interpretation. Thus
no floating result is chosen by the certificate and no integer law is imposed
on floating operands. This is a semantic specification, not exported checking
code or a claim that a native implementation has been verified.\<close>

definition lpp_stable_decode_integer ::
  "(string lp_cut_symbol,'v) lp_iterm \<Rightarrow> int option" where
  "lpp_stable_decode_integer t =
    (if \<exists>n. t = lpp_integer_value n
     then Some (THE n. t = lpp_integer_value n) else None)"

lemma lpp_stable_decode_integer_literal[simp]:
  "lpp_stable_decode_integer (lpp_integer_value n) = Some n"
  by (simp add: lpp_stable_decode_integer_def)

lemma lpp_stable_decode_integer_exact:
  "lpp_stable_decode_integer t = Some n \<longleftrightarrow> t = lpp_integer_value n"
proof
  assume decoded: "lpp_stable_decode_integer t = Some n"
  then obtain m where literal: "t = lpp_integer_value m"
    by (auto simp: lpp_stable_decode_integer_def split: if_splits)
  show "t = lpp_integer_value n" using decoded literal by simp
next
  assume "t = lpp_integer_value n"
  then show "lpp_stable_decode_integer t = Some n" by simp
qed

lemma lpp_stable_decode_binary64[simp]:
  "lpp_stable_decode_integer (lpp_binary64_value bits) = None"
  by (simp add: lpp_stable_decode_integer_def lpp_binary64_not_integer)

fun lpp_stable_profile_operation where
  "lpp_stable_profile_operation fallback f [x] =
    (case lpp_stable_decode_integer x of None \<Rightarrow> fallback f [x]
     | Some n \<Rightarrow>
       if f = LPCUser ''1:prolog_data_2b'' then Some (lpp_integer_value n)
       else if f = LPCUser ''1:prolog_data_2d'' then Some (lpp_integer_value (-n))
       else fallback f [x])"
| "lpp_stable_profile_operation fallback f [x,y] =
    (case (lpp_stable_decode_integer x, lpp_stable_decode_integer y) of
       (Some n, Some m) \<Rightarrow>
         if f = LPCUser ''2:prolog_data_2b'' then Some (lpp_integer_value (n+m))
         else if f = LPCUser ''2:prolog_data_2d'' then Some (lpp_integer_value (n-m))
         else if f = LPCUser ''2:prolog_data_2a'' then Some (lpp_integer_value (n*m))
         else if f = LPCUser ''2:prolog_data_646976'' then
           (if m = 0 then None else Some (lpp_integer_value (n div m)))
         else if f = LPCUser ''2:prolog_data_6d6f64'' then
           (if m = 0 then None else Some (lpp_integer_value (n mod m)))
         else fallback f [x,y]
     | _ \<Rightarrow> fallback f [x,y])"
| "lpp_stable_profile_operation fallback f xs = fallback f xs"

lemma lpp_stable_profile_integer_compatible:
  "lpp_stable_integer_operations (lpp_stable_profile_operation fallback)"
  by (simp add: lpp_stable_integer_operations_def)

lemma lpp_stable_profile_binary64_unary:
  "lpp_stable_profile_operation fallback f [lpp_binary64_value bits] =
    fallback f [lpp_binary64_value bits]"
  by simp

lemma lpp_stable_profile_binary64_left:
  "lpp_stable_profile_operation fallback f [lpp_binary64_value bits, y] =
    fallback f [lpp_binary64_value bits, y]"
  by simp

lemma lpp_stable_profile_binary64_right:
  "lpp_stable_profile_operation fallback f [x, lpp_binary64_value bits] =
    fallback f [x, lpp_binary64_value bits]"
  by (simp split: option.splits)

lemma lpp_stable_profile_zero_divisor:
  "lpp_stable_profile_operation fallback (LPCUser ''2:prolog_data_646976'')
    [lpp_integer_value n, lpp_integer_value 0] = None"
  "lpp_stable_profile_operation fallback (LPCUser ''2:prolog_data_6d6f64'')
    [lpp_integer_value n, lpp_integer_value 0] = None"
  by simp_all

ML \<open>
val checked = [@{thm lpp_stable_decode_integer_exact},
  @{thm lpp_stable_profile_integer_compatible},
  @{thm lpp_stable_profile_binary64_unary},
  @{thm lpp_stable_profile_binary64_left},
  @{thm lpp_stable_profile_binary64_right},
  @{thm lpp_stable_profile_zero_divisor(1)},
  @{thm lpp_stable_profile_zero_divisor(2)}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted fixed profile integer operation dependency" else ();
\<close>
end
