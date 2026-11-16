theory LP_Prolog_Scalar_Expression_Templates
 imports LP_Prolog_Scalar_Operations
begin

text \<open>Arithmetic templates preserve evaluated values of parameters while
allowing their source syntax to grow. Parameters denote actual runtime terms,
not substituted scalar literals. The existing binary64 operation table is used;
no alternate source execution relation is introduced.\<close>

datatype lpp_scalar_template =
    LPPScalarParameter string
  | LPPScalarLiteral lpp_machine_scalar
  | LPPScalarBinary string lpp_scalar_template lpp_scalar_template

fun lpp_scalar_template_term where
 "lpp_scalar_template_term (LPPScalarParameter x) = Var x"
| "lpp_scalar_template_term (LPPScalarLiteral v) = lpp_machine_term v"
| "lpp_scalar_template_term (LPPScalarBinary f a b) =
    Fun (LPCUser f) [lpp_scalar_template_term a,lpp_scalar_template_term b]"

fun lpp_scalar_template_evaluate where
 "lpp_scalar_template_evaluate value_table (LPPScalarParameter x) =
    (case value_table x of Some v \<Rightarrow> if lpp_machine_valid v then Some v else None | None \<Rightarrow> None)"
| "lpp_scalar_template_evaluate value_table (LPPScalarLiteral v) =
    (if lpp_machine_valid v then Some v else None)"
| "lpp_scalar_template_evaluate value_table (LPPScalarBinary f a b) =
    (if lpp_scalar_binary_name f then
       (case (lpp_scalar_template_evaluate value_table a,lpp_scalar_template_evaluate value_table b) of
         (Some x,Some y) \<Rightarrow> lpp_scalar_binary f x y | _ \<Rightarrow> None)
     else None)"

lemma lpp_scalar_template_valid:
 "lpp_scalar_template_evaluate value_table e = Some v \<Longrightarrow> lpp_machine_valid v"
 by (cases e) (auto split: option.splits prod.splits if_splits dest: lpp_scalar_binary_valid)

lemma lpp_scalar_template_sound:
 assumes checked: "lpp_scalar_template_evaluate value_table e = Some v"
   and parameters: "\<And>x w. value_table x = Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
 shows "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
   (lp_ieval (lpp_scalar_template_term e) eta) (lpp_machine_value v)"
 using checked
proof (induct e arbitrary: v)
 case (LPPScalarParameter x)
 have found: "value_table x = Some v"
   using LPPScalarParameter.prems by (auto split: option.splits if_splits)
 show ?case using parameters[OF found] by simp
next
 case (LPPScalarLiteral w)
 have valid: "lpp_machine_valid w" and same: "v=w"
   using LPPScalarLiteral.prems by (auto split: if_splits)
 show ?case unfolding same
   by (simp only: lpp_scalar_template_term.simps lpp_machine_term_eval;
       rule lpp_stable_scalar_evaluation.scalar[OF lpp_machine_scalar_fraction[OF valid]])
next
 case (LPPScalarBinary f a b)
 obtain x y where left: "lpp_scalar_template_evaluate value_table a=Some x"
   and right: "lpp_scalar_template_evaluate value_table b=Some y"
   and operated: "lpp_scalar_binary f x y=Some v"
   and name: "lpp_scalar_binary_name f"
   using LPPScalarBinary.prems by (auto split: option.splits prod.splits if_splits)
 have operation: "lpp_binary64_profile_operation fallback (LPCUser f)
     [lpp_machine_value x,lpp_machine_value y]=Some (lpp_machine_value v)"
   using lpp_scalar_binary_profile[OF lpp_scalar_template_valid[OF left]
     lpp_scalar_template_valid[OF right] name] operated by simp
 have valid: "lpp_machine_valid v" by (rule lpp_scalar_binary_valid[OF operated])
 show ?case by (simp only: lpp_scalar_template_term.simps lp_ieval.simps list.map;
   rule lpp_stable_scalar_evaluation.binary[OF LPPScalarBinary.hyps(1)[OF left]
     LPPScalarBinary.hyps(2)[OF right] operation lpp_machine_scalar_fraction[OF valid]])
qed

ML \<open>
val checked = [@{thm lpp_scalar_template_valid}, @{thm lpp_scalar_template_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar expression template dependency" else ();
\<close>
end
