theory LP_Prolog_Binary64_Operations
 imports LP_Prolog_Binary64_Rounding LP_Prolog_Stable_Profile_Operations
begin

datatype lpp_machine_scalar = LPPMachineInteger int | LPPMachineFloat nat
fun lpp_machine_valid where
 "lpp_machine_valid (LPPMachineInteger n)=True"
| "lpp_machine_valid (LPPMachineFloat b)=lpp_binary64_finite b"
fun lpp_machine_value where
 "lpp_machine_value (LPPMachineInteger n)=lpp_integer_value n"
| "lpp_machine_value (LPPMachineFloat b)=lpp_binary64_value b"
fun lpp_machine_fraction where
 "lpp_machine_fraction (LPPMachineInteger n)=(n,1)"
| "lpp_machine_fraction (LPPMachineFloat b)=lpp_binary64_fraction b"

lemma lpp_machine_value_injective:
 "lpp_machine_valid a \<Longrightarrow> lpp_machine_valid b \<Longrightarrow>
  lpp_machine_value a=lpp_machine_value b \<Longrightarrow> a=b"
 by (cases a; cases b)
   (auto simp: lpp_binary64_finite_def lpp_binary64_not_integer lpp_binary64_not_integer[symmetric]
     intro: lpp_binary64_value_injective)

lemma lpp_machine_scalar_fraction:
 "lpp_machine_valid a \<Longrightarrow>
  lpp_scalar_fraction (lpp_machine_value a)
    (fst (lpp_machine_fraction a)) (snd (lpp_machine_fraction a))"
 by (cases a) (auto simp: lpp_scalar_fraction_def)

definition lpp_machine_decode where
 "lpp_machine_decode t =
  (if \<exists>a. lpp_machine_valid a \<and> lpp_machine_value a=t
   then Some (THE a. lpp_machine_valid a \<and> lpp_machine_value a=t) else None)"

lemma lpp_machine_decode_value:
 assumes valid: "lpp_machine_valid a"
 shows "lpp_machine_decode (lpp_machine_value a)=Some a"
proof -
 have unique: "(THE b. lpp_machine_valid b \<and> lpp_machine_value b=lpp_machine_value a)=a"
   by (rule the_equality) (use valid lpp_machine_value_injective in auto)
 show ?thesis using valid unique by (auto simp: lpp_machine_decode_def)
qed

definition lpp_machine_rounded where
 "lpp_machine_rounded negative_zero n d =
  (case lpp_binary64_round_fraction negative_zero n d of None \<Rightarrow> None
   | Some bits \<Rightarrow> if lpp_binary64_finite bits then Some (LPPMachineFloat bits) else None)"
fun lpp_machine_float where
 "lpp_machine_float (LPPMachineInteger n)=
    (case lpp_machine_rounded False n 1 of Some (LPPMachineFloat b) \<Rightarrow> Some b | _ \<Rightarrow> None)"
| "lpp_machine_float (LPPMachineFloat b)=(if lpp_binary64_finite b then Some b else None)"

definition lpp_binary64_negative where "lpp_binary64_negative b = (b\<ge>(2::nat)^63)"
definition lpp_binary64_negate where
 "lpp_binary64_negate b = (if lpp_binary64_negative b then b-2^63 else b+2^63)"

definition lpp_machine_float_binary where
 "lpp_machine_float_binary f a b =
  (case (lpp_machine_float a,lpp_machine_float b) of (Some x,Some y) \<Rightarrow>
   (let (n,d)=lpp_binary64_fraction x; (m,e)=lpp_binary64_fraction y;
        sx=lpp_binary64_negative x; sy=lpp_binary64_negative y
    in if f=''2:prolog_data_2b'' then lpp_machine_rounded (sx\<and>sy) (n*e+m*d) (d*e)
       else if f=''2:prolog_data_2d'' then lpp_machine_rounded (sx\<and>\<not>sy) (n*e-m*d) (d*e)
       else if f=''2:prolog_data_2a'' then lpp_machine_rounded (sx\<noteq>sy) (n*m) (d*e)
       else if f=''2:prolog_data_2f'' then lpp_machine_rounded (sx\<noteq>sy) (n*e) (d*m)
       else None)
   | _ \<Rightarrow> None)"

fun lpp_machine_binary where
 "lpp_machine_binary f (LPPMachineInteger n) (LPPMachineInteger m) =
   (if f=''2:prolog_data_2b'' then Some (LPPMachineInteger (n+m))
    else if f=''2:prolog_data_2d'' then Some (LPPMachineInteger (n-m))
    else if f=''2:prolog_data_2a'' then Some (LPPMachineInteger (n*m))
    else lpp_machine_float_binary f (LPPMachineInteger n) (LPPMachineInteger m))"
| "lpp_machine_binary f a b = lpp_machine_float_binary f a b"

lemma lpp_machine_rounded_valid:
 "lpp_machine_rounded negative_zero n d=Some v \<Longrightarrow> lpp_machine_valid v"
 by (auto simp: lpp_machine_rounded_def split: option.splits if_splits)
lemma lpp_machine_float_binary_valid:
 "lpp_machine_float_binary f a b=Some v \<Longrightarrow> lpp_machine_valid v"
 by (auto simp: lpp_machine_float_binary_def Let_def split: option.splits prod.splits if_splits
   dest: lpp_machine_rounded_valid)
lemma lpp_machine_binary_valid:
 "lpp_machine_binary f a b=Some v \<Longrightarrow> lpp_machine_valid v"
 by (cases a; cases b) (auto split: if_splits dest: lpp_machine_float_binary_valid)

definition lpp_binary64_fallback where
 "lpp_binary64_fallback fallback f ts =
  (case (f,ts) of (LPCUser name,[x,y]) \<Rightarrow>
     if name\<in>{''2:prolog_data_2b'',''2:prolog_data_2d'',''2:prolog_data_2a'',''2:prolog_data_2f''}
     then (case (lpp_machine_decode x,lpp_machine_decode y) of
       (Some a,Some b) \<Rightarrow> map_option lpp_machine_value (lpp_machine_binary name a b)
       | _ \<Rightarrow> fallback f ts)
     else fallback f ts
   | _ \<Rightarrow> fallback f ts)"

definition lpp_binary64_profile_operation where
 "lpp_binary64_profile_operation fallback = lpp_stable_profile_operation (lpp_binary64_fallback fallback)"

lemma lpp_binary64_profile_integer_compatible:
 "lpp_stable_integer_operations (lpp_binary64_profile_operation fallback)"
 by (simp add: lpp_binary64_profile_operation_def lpp_stable_profile_integer_compatible)

ML \<open>
val checked = [@{thm lpp_machine_value_injective}, @{thm lpp_machine_decode_value},
 @{thm lpp_machine_scalar_fraction}, @{thm lpp_machine_binary_valid},
 @{thm lpp_binary64_profile_integer_compatible}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted binary64 operation dependency" else ();
\<close>
end
