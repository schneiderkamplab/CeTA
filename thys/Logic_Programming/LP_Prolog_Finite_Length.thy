theory LP_Prolog_Finite_Length
 imports LP_Prolog_Finite_Is
begin

text \<open>Finite observed list spines may contain rational elements. This
relation does not assert termination of the open-list length generator.
Its eventual source domain must separately establish a finite input.\<close>
inductive lpp_list_length :: "(string lp_cut_symbol,'v) lp_iterm \<Rightarrow> nat \<Rightarrow> bool" where
  nil: "lpp_list_length (LPIFun (LPCUser ''0:prolog_data_5b5d'') []) 0"
| cons: "lpp_list_length t n \<Longrightarrow>
    lpp_list_length (LPIFun (LPCUser ''2:prolog_data_2e'') [h,t]) (Suc n)"

lemma lpp_list_length_unique:
  assumes "lpp_list_length t n" "lpp_list_length t m"
  shows "n=m"
  using assms
proof (induction arbitrary: m rule: lpp_list_length.induct)
  case nil
  then show ?case by (cases rule: lpp_list_length.cases) auto
next
  case (cons t n h)
  from cons.prems show ?case
    by (cases rule: lpp_list_length.cases) (auto intro: cons.IH)
qed

lemma lpp_list_length_subst:
  "lpp_list_length t n \<Longrightarrow> lpp_list_length (lp_isubst t sigma) n"
  by (induction rule: lpp_list_length.induct)
     (auto intro: lpp_list_length.intros)

lemma lpp_list_length_no_cyclic_spine:
  assumes cycle: "t=LPIFun (LPCUser ''2:prolog_data_2e'') [h,t]"
  shows "\<not> lpp_list_length t n"
proof
  assume "lpp_list_length t n"
  then show False using cycle
  proof (induction rule: lpp_list_length.induct)
    case nil
    then show False by simp
  next
    case (cons tail n head)
    have "tail=LPIFun (LPCUser ''2:prolog_data_2e'') [h,tail]"
      using cons.prems by auto
    with cons.IH show False by blast
  qed
qed

text \<open>Errors remain explicit, including type errors in the requested
length. A successful return must unify the output with the actual spine count.
This envelope is not yet installed in a source checker.\<close>
definition lpp_finite_length_outcome ::
  "(string lp_cut_symbol,'v) lp_iterm \<Rightarrow> (string lp_cut_symbol,'v) lp_iterm \<Rightarrow>
   (string,'v) lpp_builtin_result \<Rightarrow> bool" where
  "lpp_finite_length_outcome t a outcome =
    (outcome=LPPBuiltinError \<or> (\<exists>n. lpp_list_length t n \<and>
      outcome=(case lpp_integer_unifier a (int n) of
        None \<Rightarrow> LPPBuiltinFailure | Some mu \<Rightarrow> LPPBuiltinSuccess mu)))"

lemma lpp_finite_length_success:
  assumes "lpp_finite_length_outcome t a (LPPBuiltinSuccess mu)"
  shows "\<exists>n. lpp_list_length t n \<and> lp_isubst a mu=lpp_integer_value (int n)"
proof -
  obtain n where count: "lpp_list_length t n"
    and chosen: "lpp_integer_unifier a (int n)=Some mu"
    using assms by (auto simp: lpp_finite_length_outcome_def split: option.splits)
  have evaluated: "lp_isubst a mu=lpp_integer_value (int n)"
    by (rule lpp_integer_unifier_sound[OF chosen])
  show ?thesis using count evaluated by blast
qed

lemma lpp_finite_length_success_integer:
  assumes "lpp_finite_length_outcome t a (LPPBuiltinSuccess mu)"
  shows "lpp_is_integer (lp_isubst a mu)"
  using lpp_finite_length_success[OF assms]
  by (auto simp: lpp_is_integer_def)

lemma lpp_finite_length_success_spine:
  assumes "lpp_finite_length_outcome t a (LPPBuiltinSuccess mu)"
  shows "\<exists>n. lpp_list_length (lp_isubst t mu) n \<and>
    lp_isubst a mu=lpp_integer_value (int n)"
  using lpp_finite_length_success[OF assms] lpp_list_length_subst by blast


lemma lpp_finite_length_success_nonnegative:
  assumes "lpp_finite_length_outcome t a (LPPBuiltinSuccess mu)"
  shows "\<exists>n::int. 0\<le>n \<and> lp_isubst a mu=lpp_integer_value n"
  using lpp_finite_length_success[OF assms] by auto

ML \<open>
val checked = [@{thm lpp_list_length_unique}, @{thm lpp_list_length_subst},
  @{thm lpp_list_length_no_cyclic_spine}, @{thm lpp_finite_length_success},
  @{thm lpp_finite_length_success_integer}, @{thm lpp_finite_length_success_spine},
  @{thm lpp_finite_length_success_nonnegative}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite length dependency" else ();
\<close>
end
