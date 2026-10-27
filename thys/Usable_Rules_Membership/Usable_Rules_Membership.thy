theory Usable_Rules_Membership
  imports "SN.Usable_Rules_Impl"
begin

text \<open>Keep the existing checker and soundness theorem as specifications.
Only the executable membership representation changes; diagnostics and the full
replacement-map/argument-filter matching criterion are preserved.\<close>

fun
  check_ur_closed_term_set_rm_af :: "(('f \<times> nat) \<Rightarrow> ('f, 'v) rules) \<Rightarrow> (('f:: showl, 'v:: showl) term \<times> ('f, 'v) term) set \<Rightarrow> 'f af \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
where
  "check_ur_closed_term_set_rm_af _ _ _ (Var x) = succeed" |
  "check_ur_closed_term_set_rm_af rm ur \<pi> (Fun f ts) = do {
     let n = length ts;
     let pi = \<pi> (f, n);
     check_allm_index (\<lambda>t i. if i \<in> pi then check_ur_closed_term_set_rm_af rm ur \<pi> t else succeed) ts;
     check_allm (\<lambda>lr.
       check (lr \<in> ur \<or> \<not> matchCapRMBelow rm (fst lr) (Fun f ts)) 
        (showsl_lit (STR ''due to the subterm '') \<circ> showsl (Fun f ts) \<circ> showsl_lit (STR '' of some usable rhs, rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' should be usable.''))
     ) (rm (f,n))
   }"


lemma check_ur_closed_term_set_eq:
  "check_ur_closed_term_set_rm_af rm (set ur) \<pi> t =
    check_ur_closed_term_rm_af rm ur \<pi> t"
proof (induction t)
  case (Var x)
  show ?case by simp
next
  case (Fun f ts)
  have rec: "forallM_index (\<lambda>t i. if i \<in> \<pi> (f, length ts)
      then check_ur_closed_term_set_rm_af rm (set ur) \<pi> t else succeed) ts =
    forallM_index (\<lambda>t i. if i \<in> \<pi> (f, length ts)
      then check_ur_closed_term_rm_af rm ur \<pi> t else succeed) ts"
    by (rule forallM_index) (simp add: Fun.IH)
  show ?case by (simp only: check_ur_closed_term_set_rm_af.simps
    check_ur_closed_term_rm_af.simps Let_def rec)
qed

declare check_ur_P_closed_rm_af_def[code del]

lemma check_ur_P_closed_rm_af_indexed_code [code]:
  "check_ur_P_closed_rm_af rm ur \<pi> P =
    (let U = set ur in do {
       check_allm (\<lambda>lr. check_ur_closed_term_set_rm_af rm U \<pi> (snd lr)) ur
         <+? (\<lambda>s. showsl_lit (STR ''error when checking closure properties of rhs of usable rules\<newline>'') \<circ> s);
       check_allm (\<lambda>st. check_ur_closed_term_set_rm_af rm U \<pi> (snd st)) P
         <+? (\<lambda>s. showsl_lit (STR ''error when checking closure properties of rhs of DPs\<newline>'') \<circ> s)
     })"
  by (simp add: Let_def check_ur_closed_term_set_eq check_ur_P_closed_rm_af_def)

end
