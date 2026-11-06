theory LP_Prolog_Stable_Source
  imports LP_Prolog_Stable_Is LP_Prolog_Integer_NO
begin

text \<open>This refines the builtin parameter of the existing source relation.
The fixed arithmetic interpretation is not supplied by a certificate. Errors
remain possible wherever the previous finite envelope admitted them.\<close>

definition lpp_stable_source_builtin where
  "lpp_stable_source_builtin operation f ts outcome =
    (lpp_finite_source_builtin f ts outcome \<and>
      (if f=''2:is'' then lpp_stable_is_outcome operation (ts!0) (ts!1) outcome
       else case lpp_source_comparison f of
         None \<Rightarrow> True
       | Some (comparison,reversed) \<Rightarrow>
           lpp_stable_compare_outcome operation comparison
             (if reversed then ts!1 else ts!0)
             (if reversed then ts!0 else ts!1) outcome))"

lemma lpp_stable_source_refines_finite:
  "lpp_stable_source_builtin operation f ts outcome \<Longrightarrow>
    lpp_finite_source_builtin f ts outcome"
  by (simp add: lpp_stable_source_builtin_def)

lemma lpp_stable_source_execution_subset:
  "lpp_builtin_source P (lpp_stable_source_builtin operation) \<subseteq>
    lpp_builtin_source P lpp_finite_source_builtin"
  by (rule lpp_builtin_source_mono) (rule lpp_stable_source_refines_finite)

lemma lpp_stable_source_other:
  "f\<noteq>''2:is'' \<Longrightarrow> lpp_source_comparison f=None \<Longrightarrow>
    lpp_stable_source_builtin operation f ts outcome = lpp_finite_source_builtin f ts outcome"
  by (simp add: lpp_stable_source_builtin_def)

ML \<open>
val checked = [@{thm lpp_stable_source_refines_finite},
  @{thm lpp_stable_source_execution_subset}, @{thm lpp_stable_source_other}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable source dependency" else ();
\<close>
end
