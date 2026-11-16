theory LP_Prolog_Scalar_Domain_Expressions
 imports LP_Prolog_Scalar_Expression_Templates
begin

text \<open>Fixed scalar observations and arbitrary evaluated integers form a
product invariant. Integer observations guarantee defined integer arithmetic;
they do not assume that an unbounded accumulator repeats its value.\<close>

datatype lpp_recurrent_scalar_domain = LPPRecurrentFixed lpp_machine_scalar | LPPRecurrentInteger
fun lpp_recurrent_scalar_member where
 "lpp_recurrent_scalar_member (LPPRecurrentFixed w) v = (lpp_machine_valid v \<and> v=w)"
| "lpp_recurrent_scalar_member LPPRecurrentInteger (LPPMachineInteger n) = True"
| "lpp_recurrent_scalar_member LPPRecurrentInteger (LPPMachineFloat b) = False"
fun lpp_recurrent_integer_domain where
 "lpp_recurrent_integer_domain LPPRecurrentInteger = True"
| "lpp_recurrent_integer_domain (LPPRecurrentFixed (LPPMachineInteger n)) = True"
| "lpp_recurrent_integer_domain _ = False"
definition lpp_recurrent_total_integer_operator where
 "lpp_recurrent_total_integer_operator f =
   (f\<in>{''2:prolog_data_2b'',''2:prolog_data_2d'',''2:prolog_data_2a''})"
fun lpp_recurrent_nonzero_integer where
 "lpp_recurrent_nonzero_integer (LPPRecurrentFixed (LPPMachineInteger n)) = (n\<noteq>0)"
| "lpp_recurrent_nonzero_integer _ = False"
fun lpp_recurrent_scalar_binary where
 "lpp_recurrent_scalar_binary f (LPPRecurrentFixed x) (LPPRecurrentFixed y) =
   map_option LPPRecurrentFixed (lpp_scalar_binary f x y)"
| "lpp_recurrent_scalar_binary f a b =
   (if lpp_recurrent_integer_domain a \<and> lpp_recurrent_integer_domain b \<and>
      (lpp_recurrent_total_integer_operator f \<or>
       lpp_scalar_integer_binary_name f \<and> lpp_recurrent_nonzero_integer b) then Some LPPRecurrentInteger else None)"

lemma lpp_recurrent_member_valid:
 "lpp_recurrent_scalar_member d v \<Longrightarrow> lpp_machine_valid v"
 by (cases d; cases v) auto
lemma lpp_recurrent_integer_member:
 "lpp_recurrent_integer_domain d \<Longrightarrow> lpp_recurrent_scalar_member d v \<Longrightarrow>
   \<exists>n. v=LPPMachineInteger n"
 by (cases d; cases v) (auto split: lpp_machine_scalar.splits)
lemma lpp_recurrent_scalar_binary_sound:
 assumes checked: "lpp_recurrent_scalar_binary f a b=Some d"
   and left: "lpp_recurrent_scalar_member a x" and right: "lpp_recurrent_scalar_member b y"
 shows "\<exists>v. lpp_scalar_binary f x y=Some v \<and> lpp_recurrent_scalar_member d v"
 using checked left right
 by (cases a; cases b; cases x; cases y)
   (auto simp: lpp_recurrent_total_integer_operator_def lpp_scalar_integer_binary_name_def
     split: option.splits if_splits lpp_machine_scalar.splits
     dest: lpp_scalar_binary_valid lpp_machine_float_binary_valid)

fun lpp_recurrent_template_domain where
 "lpp_recurrent_template_domain domains (LPPScalarParameter x) = domains x"
| "lpp_recurrent_template_domain domains (LPPScalarLiteral v) =
   (if lpp_machine_valid v then Some (LPPRecurrentFixed v) else None)"
| "lpp_recurrent_template_domain domains (LPPScalarBinary f a b) =
   (if lpp_scalar_binary_name f then
    (case (lpp_recurrent_template_domain domains a,lpp_recurrent_template_domain domains b) of
     (Some x,Some y) \<Rightarrow> lpp_recurrent_scalar_binary f x y | _ \<Rightarrow> None)
    else None)"

definition lpp_recurrent_domain_environment where
 "lpp_recurrent_domain_environment operation domains eta =
   (\<forall>x d. domains x=Some d \<longrightarrow> (\<exists>v. lpp_recurrent_scalar_member d v \<and>
     lpp_stable_scalar_evaluation operation (eta x) (lpp_machine_value v)))"

lemma lpp_recurrent_template_sound:
 assumes checked: "lpp_recurrent_template_domain domains e=Some d"
   and parameters: "lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback) domains eta"
 shows "\<exists>v. lpp_recurrent_scalar_member d v \<and>
   lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lp_ieval (lpp_scalar_template_term e) eta) (lpp_machine_value v)"
 using checked
proof (induct e arbitrary: d)
 case (LPPScalarParameter x)
 show ?case using parameters LPPScalarParameter.prems
   by (auto simp: lpp_recurrent_domain_environment_def)
next
 case (LPPScalarLiteral w)
 have valid: "lpp_machine_valid w" and same: "d=LPPRecurrentFixed w"
   using LPPScalarLiteral.prems by (auto split: if_splits)
 have evaluation: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lp_ieval (lpp_machine_term w) eta) (lpp_machine_value w)"
   by (simp only: lpp_machine_term_eval;
       rule lpp_stable_scalar_evaluation.scalar[OF lpp_machine_scalar_fraction[OF valid]])
 show ?case using valid same evaluation by auto
next
 case (LPPScalarBinary f a b)
 obtain da db where left: "lpp_recurrent_template_domain domains a=Some da"
   and right: "lpp_recurrent_template_domain domains b=Some db"
   and operated: "lpp_recurrent_scalar_binary f da db=Some d"
   and name: "lpp_scalar_binary_name f"
   using LPPScalarBinary.prems by (auto split: option.splits prod.splits if_splits)
 obtain x where mx: "lpp_recurrent_scalar_member da x"
   and ex: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lp_ieval (lpp_scalar_template_term a) eta) (lpp_machine_value x)"
   using LPPScalarBinary.hyps(1)[OF left] by blast
 obtain y where my: "lpp_recurrent_scalar_member db y"
   and ey: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lp_ieval (lpp_scalar_template_term b) eta) (lpp_machine_value y)"
   using LPPScalarBinary.hyps(2)[OF right] by blast
 obtain v where operation: "lpp_scalar_binary f x y=Some v"
   and member: "lpp_recurrent_scalar_member d v"
   using lpp_recurrent_scalar_binary_sound[OF operated mx my] by blast
 have profile: "lpp_binary64_profile_operation fallback (LPCUser f)
     [lpp_machine_value x,lpp_machine_value y]=Some (lpp_machine_value v)"
   using lpp_scalar_binary_profile[OF lpp_recurrent_member_valid[OF mx]
     lpp_recurrent_member_valid[OF my] name] operation by simp
 have evaluation: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lp_ieval (lpp_scalar_template_term (LPPScalarBinary f a b)) eta) (lpp_machine_value v)"
   by (simp only: lpp_scalar_template_term.simps lp_ieval.simps list.map;
     rule lpp_stable_scalar_evaluation.binary[OF ex ey profile
       lpp_machine_scalar_fraction[OF lpp_recurrent_member_valid[OF member]]])
 show ?case using member evaluation by blast
qed

ML \<open>
val checked = [@{thm lpp_recurrent_template_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted recurrent scalar domain dependency" else ();
\<close>
end
