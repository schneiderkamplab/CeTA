theory LP_Prolog_Success_Magnitude
 imports LP_Prolog_Stable_Magnitude_Algebra
begin

datatype lpp_magnitude_bound = LPPMKnown nat | LPPMZero | LPPMQuotient lpp_magnitude_bound

fun lpp_check_magnitude_bound where
  "lpp_check_magnitude_bound known t (LPPMKnown i) = (i<length known \<and> known!i=t)"
| "lpp_check_magnitude_bound known t LPPMZero = (t=lpp_expression_term (LPPEConstant 0))"
| "lpp_check_magnitude_bound known t (LPPMQuotient p) =
    (case t of Fun f [a,b] \<Rightarrow> f=LPCUser ''2:prolog_data_2f2f'' \<and>
      lpp_check_magnitude_bound known a p | _ \<Rightarrow> False)"

lemma lpp_check_magnitude_bound_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_magnitude_bound known t receipt"
    and known: "\<And>v. v\<in>set known \<Longrightarrow> abs (lpp_stable_scaled_bound operation (lp_ieval v eta))\<le>M"
    and nonnegative: "0\<le>M"
  shows "abs (lpp_stable_scaled_bound operation (lp_ieval t eta))\<le>M"
  using checked known
proof (induction receipt arbitrary: t)
  case (LPPMKnown i)
  then have "t\<in>set known" by (auto intro: nth_mem)
  then show ?case by (rule known)
next
  case LPPMZero
  then have zero: "t=lpp_expression_term (LPPEConstant 0)" by simp
  show ?case using nonnegative
    by (simp add: zero lpp_expression_term.simps lpp_stable_scaled_integer[OF lpp_stable_integer_literal])
next
  case (LPPMQuotient receipt)
  obtain a b where shape: "t=Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]"
    and checked: "lpp_check_magnitude_bound known a receipt"
    using LPPMQuotient.prems(1) by (auto split: term.splits list.splits)
  have bound: "abs (lpp_stable_scaled_bound operation (lp_ieval a eta))\<le>M"
    by (rule LPPMQuotient.IH[OF checked known])
  show ?case using lpp_stable_quotient_abs_bound[OF compatible, of "lp_ieval a eta" "lp_ieval b eta"] bound
    by (simp add: shape)
qed

text \<open>Return summaries are inducted over finite successful derivations.
The clause premise covers every clause in the complete shared success program;
there is no hypothesis that a helper terminates or always returns.\<close>

theorem lpp_magnitude_success_invariant:
  assumes success: "lpp_guarded_success P E a"
    and clauses: "\<And>h bs gs eta. (h,bs,gs)\<in>set P \<Longrightarrow>
      list_all (lpp_success_guard_holds E eta) gs \<Longrightarrow>
      list_all (\<lambda>b. magnitude_property (lpp_success_atom_eval b eta)) bs \<Longrightarrow>
      magnitude_property (lpp_success_atom_eval h eta)"
  shows "magnitude_property a"
  using success by (induction rule: lpp_guarded_success.induct)
    (auto intro: clauses simp: list_all_iff)

ML \<open>
val checked = [@{thm lpp_check_magnitude_bound_sound}, @{thm lpp_magnitude_success_invariant}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted magnitude return dependency" else ();
\<close>
end
