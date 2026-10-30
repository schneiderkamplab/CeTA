theory LP_Prolog_Integer_Builtins
  imports LP_Prolog_Arithmetic_Semantics
begin

text \<open>These primitive rules cover integer evaluation after a checked
integer-expression obligation. They are not an exhaustive arithmetic semantics
on arbitrary inputs. A source graph must establish that obligation at each
arithmetic call; unsupported evaluations cannot be discarded as failures.
Unification of the evaluated integer inspects only the left root, so rational
terms do not require a finite-tree assumption.\<close>

fun lpp_integer_unifier where
  "lpp_integer_unifier (LPIVar x) n = Some (LPIVar(x:=lpp_integer_value n))"
| "lpp_integer_unifier (LPIFun f ts) n =
    (if LPIFun f ts=lpp_integer_value n then Some LPIVar else None)"

lemma lpp_integer_unifier_sound:
  "lpp_integer_unifier a n=Some mu \<Longrightarrow> lp_isubst a mu=lpp_integer_value n"
  by (cases a) (auto split: if_splits)

lemma lpp_integer_unifier_complete:
  "lpp_integer_unifier a n=None \<longleftrightarrow> \<not>(\<exists>sigma. lp_isubst a sigma=lpp_integer_value n)"
  by (cases a) (auto simp: lpp_integer_value_def split: if_splits)

lemma lpp_integer_unifier_most_general:
  assumes chosen: "lpp_integer_unifier a n=Some mu"
    and unifies: "lp_isubst a sigma=lpp_integer_value n"
  shows "lp_isubst (mu x) sigma=sigma x"
  using chosen unifies by (cases a) (auto split: if_splits)

definition lpp_integer_is_outcome where
  "lpp_integer_is_outcome a e outcome = (\<exists>n. lpp_integer_evaluation e n \<and>
    outcome=(case lpp_integer_unifier a n of None \<Rightarrow> LPPBuiltinFailure
      | Some mu \<Rightarrow> LPPBuiltinSuccess mu))"

lemma lpp_integer_is_outcome_exact:
  assumes evaluated: "lpp_integer_evaluation e n"
  shows "lpp_integer_is_outcome a e outcome \<longleftrightarrow>
    outcome=(case lpp_integer_unifier a n of None \<Rightarrow> LPPBuiltinFailure
      | Some mu \<Rightarrow> LPPBuiltinSuccess mu)"
  using lpp_integer_evaluation_unique[OF evaluated]
  by (auto simp: lpp_integer_is_outcome_def intro: evaluated)

lemma lpp_checked_is_outcome:
  assumes checked: "lpp_expression_check K e"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lpp_integer_is_outcome a (lp_ieval (lpp_expression_term e) eta) outcome \<longleftrightarrow>
    outcome=(case lpp_integer_unifier a (lpp_expression_value e rho) of
      None \<Rightarrow> LPPBuiltinFailure | Some mu \<Rightarrow> LPPBuiltinSuccess mu)"
  by (rule lpp_integer_is_outcome_exact[OF lpp_expression_evaluation[OF checked typed]])

lemma lpp_integer_is_success_evidence:
  assumes outcome: "lpp_integer_is_outcome a e (LPPBuiltinSuccess mu)"
  shows "lpp_integer_result e (lp_isubst a mu) \<and> lp_isubst e mu=e"
proof -
  obtain n where evaluated: "lpp_integer_evaluation e n"
    and chosen: "lpp_integer_unifier a n=Some mu"
    using outcome by (auto simp: lpp_integer_is_outcome_def split: option.splits)
  show ?thesis using lpp_integer_unifier_sound[OF chosen]
    lpp_integer_evaluation_subst[OF evaluated] evaluated
    by (auto simp: lpp_integer_result_def)
qed

datatype lpp_integer_comparison = LPPIntLess | LPPIntLessEqual | LPPIntEqual | LPPIntNotEqual
fun lpp_integer_compare where
  "lpp_integer_compare LPPIntLess n m = (n<m)"
| "lpp_integer_compare LPPIntLessEqual n m = (n\<le>m)"
| "lpp_integer_compare LPPIntEqual n m = (n=m)"
| "lpp_integer_compare LPPIntNotEqual n m = (n\<noteq>m)"

definition lpp_integer_compare_outcome ::
  "lpp_integer_comparison \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm \<Rightarrow>
    (string lp_cut_symbol,'w) lp_iterm \<Rightarrow> (string,'w) lpp_builtin_result \<Rightarrow> bool" where
  "lpp_integer_compare_outcome comparison a b outcome =
    (\<exists>n m. lpp_integer_evaluation a n \<and> lpp_integer_evaluation b m \<and>
      outcome=(if lpp_integer_compare comparison n m then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure))"

lemma lpp_integer_compare_outcome_exact:
  assumes left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
  shows "lpp_integer_compare_outcome comparison a b outcome \<longleftrightarrow>
    outcome=(if lpp_integer_compare comparison n m then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
  using lpp_integer_evaluation_unique[OF left] lpp_integer_evaluation_unique[OF right]
  by (auto simp: lpp_integer_compare_outcome_def intro: left right)

text \<open>The source stack and saved answer environments remain the shared
LP-with-cut stack. The following local rule applies to any interpreted builtin
extension whose outcomes agree on this checked call.\<close>

lemma lpp_checked_is_failure_step:
  assumes evaluated: "lpp_integer_evaluation e n"
    and fails: "lpp_integer_unifier a n=None"
    and exact: "\<And>outcome. U ''2:is'' [a,e] outcome = lpp_integer_is_outcome a e outcome"
  shows "lpp_answer_transition P lpp_builtin_signature U
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt
    \<longleftrightarrow> event=None \<and> tt=saved"
proof (rule lpp_builtin_failure_only)
  show "(''2:is'',length [a,e])\<in>lpp_builtin_signature"
    by (simp add: lpp_builtin_signature_def numeral_2_eq_2)
  fix outcome
  show "U ''2:is'' [a,e] outcome \<longleftrightarrow> outcome=LPPBuiltinFailure"
    by (simp only: exact lpp_integer_is_outcome_exact[OF evaluated] fails option.case)
qed

lemma lpp_checked_is_success_step:
  assumes evaluated: "lpp_integer_evaluation e n"
    and chosen: "lpp_integer_unifier a n=Some mu"
    and exact: "\<And>outcome. U ''2:is'' [a,e] outcome = lpp_integer_is_outcome a e outcome"
  shows "lpp_answer_transition P lpp_builtin_signature U
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt
    \<longleftrightarrow> event=None \<and>
      tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs),\<lambda>x. lp_isubst (eta x) mu)#saved"
proof (rule lpp_builtin_success_only)
  show "(''2:is'',length [a,e])\<in>lpp_builtin_signature"
    by (simp add: lpp_builtin_signature_def numeral_2_eq_2)
  fix outcome
  show "U ''2:is'' [a,e] outcome \<longleftrightarrow> outcome=LPPBuiltinSuccess mu"
    by (simp only: exact lpp_integer_is_outcome_exact[OF evaluated] chosen option.case)
qed

lemma lpp_integer_unifier_mgu:
  assumes chosen: "lpp_integer_unifier a n=Some mu"
  shows "lpc_mgu_unify a (lpp_integer_value n) gs mu"
proof (unfold lpc_mgu_unify_def, intro conjI allI impI)
  show "lp_isubst a mu=lp_isubst (lpp_integer_value n) mu"
    using lpp_integer_unifier_sound[OF chosen] by simp
next
  fix tau assume unified: "lp_isubst a tau=lp_isubst (lpp_integer_value n) tau"
  have solution: "lp_isubst a tau=lpp_integer_value n" using unified by simp
  have factor: "(\<lambda>x. lp_isubst (mu x) tau)=tau"
    by (rule ext, rule lpp_integer_unifier_most_general[OF chosen solution])
  show "\<exists>delta. lp_isubst (lp_isubst a mu) delta=lp_isubst a tau \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t mu) delta)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
    by (rule exI[of _ tau]) (simp add: lpc_isubst_comp factor)
qed

text \<open>The evaluated integer is passed to the existing cut-aware equality
step. This preserves its full-continuation most-generality condition and saved
answer stack; Prolog arithmetic does not introduce another unification engine.\<close>

lemma lpp_checked_is_uses_shared_equality:
  assumes evaluated: "lpp_integer_evaluation e n"
    and exact: "\<And>outcome. U ''2:is'' [a,e] outcome = lpp_integer_is_outcome a e outcome"
    and step: "lpp_answer_transition P lpp_builtin_signature U
      ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
  shows "lpc_answer_transition P
    ((LPCGoals (LPCUnify a (lpp_integer_value n)#gs),eta)#saved) event tt"
proof (cases "lpp_integer_unifier a n")
  case None
  have actual: "event=None \<and> tt=saved"
    using step lpp_checked_is_failure_step[where U=U, OF evaluated None exact] by blast
  have failure: "\<not>(\<exists>sigma. lp_isubst a sigma=lp_isubst (lpp_integer_value n) sigma)"
    using lpp_integer_unifier_complete[of a n] None by simp
  show ?thesis unfolding actual[THEN conjunct1] actual[THEN conjunct2]
    by (rule lpc_answer_transition.unify_fail[OF failure])
next
  case (Some mu)
  have actual: "event=None \<and>
    tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs),\<lambda>x. lp_isubst (eta x) mu)#saved"
    using step lpp_checked_is_success_step[where U=U, OF evaluated Some exact] by blast
  show ?thesis unfolding actual[THEN conjunct1] actual[THEN conjunct2]
    by (rule lpc_answer_transition.unify[OF lpp_integer_unifier_mgu[OF Some]])
qed

ML \<open>
val checked = [@{thm lpp_integer_unifier_sound}, @{thm lpp_integer_unifier_complete},
  @{thm lpp_integer_unifier_most_general}, @{thm lpp_checked_is_outcome},
  @{thm lpp_integer_compare_outcome_exact}, @{thm lpp_checked_is_failure_step},
  @{thm lpp_checked_is_success_step}, @{thm lpp_checked_is_uses_shared_equality}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted integer builtin dependency" else ();
\<close>
end
