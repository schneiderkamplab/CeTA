theory LP_Prolog_Integer_Recurrence_Failure
  imports LP_Prolog_Integer_Recurrence_Selection
begin

definition lpp_recurrence_arguments where
  "lpp_recurrence_arguments xs ns x = (case map_of (zip xs ns) x of None \<Rightarrow> 0 | Some n \<Rightarrow> n)"

lemma lpp_recurrence_arguments_exact:
  assumes lengths: "length xs=length ns" and distinct: "distinct xs"
  shows "map (lpp_recurrence_arguments xs ns) xs=ns"
proof (rule nth_equalityI)
  show "length (map (lpp_recurrence_arguments xs ns) xs)=length ns" using lengths by simp
next
  fix i assume index: "i<length (map (lpp_recurrence_arguments xs ns) xs)"
  have bound: "i<length xs" using index by simp
  have target_bound: "i<length ns" using bound lengths by simp
  show "map (lpp_recurrence_arguments xs ns) xs ! i=ns ! i"
    using map_of_zip_nth[OF lengths distinct target_bound]
    by (simp add: lpp_recurrence_arguments_def bound)
qed

record lpp_arithmetic_failure =
  lpp_failure_clause :: nat
  lpp_failure_variables :: "string list"
  lpp_failure_prefix :: "lpp_recurrence_operation list"
  lpp_failure_predicate :: string
  lpp_failure_comparison :: lpp_integer_comparison
  lpp_failure_reversed :: bool
  lpp_failure_left :: "string lpp_integer_expression"
  lpp_failure_right :: "string lpp_integer_expression"

definition lpp_failure_operation where
  "lpp_failure_operation r = LPPRGuard (lpp_failure_predicate r) (lpp_failure_comparison r)
    (lpp_failure_reversed r) (lpp_failure_left r) (lpp_failure_right r)"

definition lpp_arithmetic_failure_shape where
  "lpp_arithmetic_failure_shape P f arity r =
    (lpp_failure_clause r<length P \<and>
     length (lpp_failure_variables r)=arity \<and> distinct (lpp_failure_variables r) \<and>
     P!lpp_failure_clause r=(Fun (LPCUser f) (map Var (lpp_failure_variables r)),
       map lpp_recurrence_goal (lpp_failure_prefix r) @
       lpp_recurrence_goal (lpp_failure_operation r)#
       drop (length (lpp_failure_prefix r)+1) (snd (P!lpp_failure_clause r))) \<and>
     lpp_recurrence_check (lpp_failure_variables r)
       (lpp_failure_prefix r @ [lpp_failure_operation r]))"

definition lpp_arithmetic_failure_holds where
  "lpp_arithmetic_failure_holds r ns =
    (let rho=lpp_recurrence_arguments (lpp_failure_variables r) ns;
         final=lpp_recurrence_values (lpp_failure_prefix r) rho
     in lpp_recurrence_guards (lpp_failure_prefix r) rho \<and>
       \<not>lpp_integer_compare (lpp_failure_comparison r)
         (lpp_expression_value (if lpp_failure_reversed r then lpp_failure_right r else lpp_failure_left r) final)
         (lpp_expression_value (if lpp_failure_reversed r then lpp_failure_left r else lpp_failure_right r) final))"

lemma lpp_recurrence_check_append:
  "lpp_recurrence_check K (ops@rest) =
    (lpp_recurrence_check K ops \<and> lpp_recurrence_check (lpp_recurrence_known K ops) rest)"
proof (induct ops arbitrary: K)
  case Nil show ?case by simp
next
  case (Cons op ops)
  show ?case by (cases op) (simp_all add: Cons.hyps)
qed

lemma lpp_checked_arithmetic_failure_restores_stack:
  assumes shape: "lpp_arithmetic_failure_shape P f (length ns) r"
    and fails: "lpp_arithmetic_failure_holds r ns"
  shows "(LPCClause [LPCAtom (LPIFun (LPCUser f) (map lpp_integer_value ns))]
      (lpp_failure_clause r) mark#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?xs = "lpp_failure_variables r"
  let ?rho = "lpp_recurrence_arguments ?xs ns"
  have exact: "map ?rho ?xs=ns"
    by (rule lpp_recurrence_arguments_exact) (use shape in \<open>auto simp: lpp_arithmetic_failure_shape_def\<close>)
  have call_value: "lp_ieval (Fun (LPCUser f) (map Var ?xs)) (lpp_recurrence_environment ?xs ?rho)=
      LPIFun (LPCUser f) (map lpp_integer_value ns)"
    using arg_cong[OF exact, of "map lpp_integer_value"]
    by (simp add: lpp_recurrence_environment_def map_map o_def cong: map_cong)
  have step: "(LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?xs))
      (lpp_recurrence_environment ?xs ?rho))] (lpp_failure_clause r) mark#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    by (rule lpp_recurrence_selected_clause_failure[
        where ops="lpp_failure_prefix r" and g="lpp_failure_predicate r"
          and c="lpp_failure_comparison r" and reversed="lpp_failure_reversed r"
          and a="lpp_failure_left r" and b="lpp_failure_right r"
          and rest="drop (length (lpp_failure_prefix r)+1) (snd (P!lpp_failure_clause r))"])
      (use shape fails in \<open>auto simp: lpp_arithmetic_failure_shape_def lpp_arithmetic_failure_holds_def
        lpp_failure_operation_def lpp_recurrence_check_append Let_def\<close>)
  show ?thesis using step by (simp only: call_value)
qed

ML \<open>
val checked = [@{thm lpp_checked_arithmetic_failure_restores_stack}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted arithmetic failure receipt dependency" else ();
\<close>
end
