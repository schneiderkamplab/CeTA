theory LP_Prolog_Partial_Integer_Interface
  imports LP_Prolog_Partial_Integer_Iteration LP_Prolog_Integer_Recurrence_Failure
begin

definition lpp_partial_arguments where
  "lpp_partial_arguments H actuals x =
    (case map_of (zip H actuals) x of None \<Rightarrow> LPIVar x | Some t \<Rightarrow> t)"

definition lpp_partial_observations where
  "lpp_partial_observations positions ns actuals =
    (length actuals=length ns \<and> list_all (\<lambda>i. i<length ns \<and>
      actuals!i=lpp_integer_value (ns!i)) positions)"

lemma lpp_partial_arguments_nth:
  assumes lengths: "length H=length actuals" and distinct: "distinct H"
    and bound: "i<length H"
  shows "lpp_partial_arguments H actuals (H!i)=actuals!i"
  using map_of_zip_nth[OF lengths distinct, of i] bound lengths
  by (simp add: lpp_partial_arguments_def)

lemma lpp_partial_arguments_exact:
  assumes lengths: "length H=length actuals" and distinct: "distinct H"
  shows "map (lpp_partial_arguments H actuals) H=actuals"
  by (rule nth_equalityI) (use lengths lpp_partial_arguments_nth[OF lengths distinct] in auto)

lemma lpp_partial_observed_head:
  assumes bounds: "list_all (\<lambda>i. i<length H) positions"
    and member: "x\<in>set (map ((!) H) positions)"
  shows "x\<in>set H"
  using assms by (auto simp: list_all_iff intro: nth_mem)

lemma lpp_partial_observed_argument:
  assumes lengths: "length H=length ns" and distinct: "distinct H"
    and observations: "lpp_partial_observations positions ns actuals"
    and member: "x\<in>set (map ((!) H) positions)"
  shows "lpp_partial_arguments H actuals x=lpp_integer_value (lpp_recurrence_arguments H ns x)"
proof -
  obtain i where index: "i\<in>set positions" and x: "x=H!i" using member by auto
  have bound: "i<length H" and observed_value: "actuals!i=lpp_integer_value (ns!i)"
    and args_length: "length H=length actuals"
    using observations index lengths by (auto simp: lpp_partial_observations_def list_all_iff)
  have numeric: "lpp_recurrence_arguments H ns (H!i)=ns!i"
    using map_of_zip_nth[OF lengths distinct, of i] bound lengths
    by (simp add: lpp_recurrence_arguments_def)
  show ?thesis using lpp_partial_arguments_nth[OF args_length distinct bound] observed_value numeric x by simp
qed

lemma lpp_partial_check_append:
  "lpp_partial_recurrence_check H K (ops@rest) =
    (lpp_partial_recurrence_check H K ops \<and>
      lpp_partial_recurrence_check H (lpp_recurrence_known K ops) rest)"
proof (induct ops arbitrary: K)
  case Nil show ?case by simp
next
  case (Cons op ops)
  show ?case by (cases op) (simp_all add: Cons.hyps)
qed

ML \<open>
val checked = [@{thm lpp_partial_observed_argument}, @{thm lpp_partial_arguments_exact},
  @{thm lpp_partial_check_append}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial integer interface dependency" else ();
\<close>
end
