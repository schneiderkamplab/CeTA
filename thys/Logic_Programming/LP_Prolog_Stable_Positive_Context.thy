theory LP_Prolog_Stable_Positive_Context
 imports LP_Prolog_Stable_Positive_Quotient LP_Prolog_Stable_Return_Context
begin

datatype 'v lpp_positive_receipt =
    LPPPositiveLiteral int
  | LPPPositiveIntegerLower nat nat "(string lp_cut_symbol,'v) term"
  | LPPPositiveEquation nat nat bool "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPPositiveQuotient nat nat nat nat
      "(string lp_cut_symbol,'v) term"
      "(string lp_cut_symbol,'v) term"
      "(string lp_cut_symbol,'v) term"

fun lpp_positive_conclusion where
  "lpp_positive_conclusion (LPPPositiveLiteral n) =
    LPPOComparison LPPIntLess (lpp_integer_term 0) (lpp_integer_term n)"
| "lpp_positive_conclusion (LPPPositiveIntegerLower i j t) =
    LPPOComparison LPPIntLessEqual (lpp_integer_term 1) t"
| "lpp_positive_conclusion (LPPPositiveEquation i j reverse a b) =
    LPPOComparison LPPIntLess (lpp_integer_term 0) (if reverse then a else b)"
| "lpp_positive_conclusion (LPPPositiveQuotient i j k l a b result) =
    LPPOComparison LPPIntLess (lpp_integer_term 0) result"

fun lpp_check_positive_receipt where
  "lpp_check_positive_receipt observations (LPPPositiveLiteral n) = (0<n)"
| "lpp_check_positive_receipt observations (LPPPositiveIntegerLower i j t) =
    (i<length observations \<and> j<length observations \<and>
     observations!i=LPPOInteger t \<and>
     observations!j=LPPOComparison LPPIntLess (lpp_integer_term 0) t)"
| "lpp_check_positive_receipt observations (LPPPositiveEquation i j reverse a b) =
    (i<length observations \<and> j<length observations \<and>
     observations!i=LPPOEquation a b \<and>
     observations!j=LPPOComparison LPPIntLess (lpp_integer_term 0) (if reverse then b else a))"
| "lpp_check_positive_receipt observations (LPPPositiveQuotient i j k l a b result) =
    (i<length observations \<and> j<length observations \<and>
     k<length observations \<and> l<length observations \<and>
     observations!i=LPPOEvaluation (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]) result \<and>
     observations!j=LPPOComparison LPPIntLess (lpp_integer_term 0) a \<and>
     observations!k=LPPOComparison LPPIntLess (lpp_integer_term 0) b \<and>
     observations!l=LPPOComparison LPPIntEqual a
       (Fun (LPCUser ''2:prolog_data_2a'') [result,b]))"

lemma lpp_checked_positive_receipt_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_positive_receipt observations receipt"
    and observed: "list_all (lpp_stable_observation_holds operation eta) observations"
  shows "lpp_stable_observation_holds operation eta (lpp_positive_conclusion receipt)"
proof (cases receipt)
  case (LPPPositiveLiteral n)
  have positive: "0<n" using checked LPPPositiveLiteral by simp
  have comparison: "lpp_stable_compare_outcome operation LPPIntLess
      (lpp_integer_value 0) (lpp_integer_value n) (LPPBuiltinSuccess LPIVar)"
    by (simp add: lpp_stable_compare_integer_exact[OF compatible lpp_integer_evaluation.literal lpp_integer_evaluation.literal]
      lpp_integer_compare_outcome_exact[OF lpp_integer_evaluation.literal lpp_integer_evaluation.literal] positive)
  show ?thesis using comparison
    by (simp add: LPPPositiveLiteral lpp_integer_term_def lpp_integer_value_def)
next
  case (LPPPositiveIntegerLower i j t)
  have at: "lpp_stable_observation_holds operation eta (observations!index)"
    if "index<length observations" for index
    using observed nth_mem[OF that] by (auto simp: list_all_iff)
  have integer: "lpp_stable_observation_holds operation eta (LPPOInteger t)"
    and positive: "lpp_stable_observation_holds operation eta
      (LPPOComparison LPPIntLess (lpp_integer_term 0) t)"
    using checked at[of i] at[of j] by (auto simp: LPPPositiveIntegerLower)
  obtain n where evaluated: "lp_ieval t eta=lpp_integer_value n"
    using integer by (auto simp: lpp_is_integer_def)
  have zero_comparison: "lpp_stable_compare_outcome operation LPPIntLess
      (lpp_integer_value 0) (lpp_integer_value n) (LPPBuiltinSuccess LPIVar)"
    using positive by (simp add: evaluated lpp_integer_term_def lpp_integer_value_def)
  have n: "0<n" using zero_comparison
    by (auto simp: lpp_stable_compare_integer_exact[OF compatible lpp_integer_evaluation.literal lpp_integer_evaluation.literal]
      lpp_integer_compare_outcome_exact[OF lpp_integer_evaluation.literal lpp_integer_evaluation.literal] split: if_splits)
  have lower: "1\<le>n" using n by arith
  have comparison: "lpp_stable_compare_outcome operation LPPIntLessEqual
      (lpp_integer_value 1) (lpp_integer_value n) (LPPBuiltinSuccess LPIVar)"
    by (simp add: lpp_stable_compare_integer_exact[OF compatible lpp_integer_evaluation.literal lpp_integer_evaluation.literal]
      lpp_integer_compare_outcome_exact[OF lpp_integer_evaluation.literal lpp_integer_evaluation.literal] lower)
  show ?thesis using comparison
    by (simp add: LPPPositiveIntegerLower evaluated lpp_integer_term_def lpp_integer_value_def)
next
  case (LPPPositiveEquation i j reverse a b)
  have at: "lpp_stable_observation_holds operation eta (observations!index)"
    if "index<length observations" for index
    using observed nth_mem[OF that] by (auto simp: list_all_iff)
  have equation: "lpp_stable_observation_holds operation eta (LPPOEquation a b)"
    and positive: "lpp_stable_observation_holds operation eta
      (LPPOComparison LPPIntLess (lpp_integer_term 0) (if reverse then b else a))"
    using checked at[of i] at[of j] by (auto simp: LPPPositiveEquation)
  show ?thesis using equation positive
    by (cases reverse) (simp_all add: LPPPositiveEquation)
next
  case (LPPPositiveQuotient i j k l a b result)
  have all: "lpp_stable_observation_holds operation eta observation"
    if "observation\<in>set observations" for observation
    using observed that by (simp add: list_all_iff)
  have at: "lpp_stable_observation_holds operation eta (observations!index)"
    if "index<length observations" for index
    by (rule all[OF nth_mem[OF that]])
  have evaluation: "lpp_stable_observation_holds operation eta
      (LPPOEvaluation (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]) result)"
    and numerator: "lpp_stable_observation_holds operation eta
      (LPPOComparison LPPIntLess (lpp_integer_term 0) a)"
    and denominator: "lpp_stable_observation_holds operation eta
      (LPPOComparison LPPIntLess (lpp_integer_term 0) b)"
    and exact: "lpp_stable_observation_holds operation eta
      (LPPOComparison LPPIntEqual a (Fun (LPCUser ''2:prolog_data_2a'') [result,b]))"
    using checked at[of i] at[of j] at[of k] at[of l]
    by (auto simp: LPPPositiveQuotient)
  show ?thesis
    using lpp_stable_positive_quotient_observation[OF compatible]
      evaluation numerator denominator exact
    by (simp add: LPPPositiveQuotient lpp_integer_term_def lpp_integer_value_def)
qed

fun lpp_check_positive_derivation where
  "lpp_check_positive_derivation observations [] = True"
| "lpp_check_positive_derivation observations (receipt#receipts) =
    (lpp_check_positive_receipt observations receipt \<and>
     lpp_check_positive_derivation (observations@[lpp_positive_conclusion receipt]) receipts)"

theorem lpp_checked_positive_derivation_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_positive_derivation observations receipts"
    and observed: "list_all (lpp_stable_observation_holds operation eta) observations"
  shows "list_all (lpp_stable_observation_holds operation eta)
    (observations@map lpp_positive_conclusion receipts)"
  using checked observed
proof (induction receipts arbitrary: observations)
  case Nil
  then show ?case by simp
next
  case (Cons receipt receipts)
  have step: "lpp_stable_observation_holds operation eta (lpp_positive_conclusion receipt)"
    by (rule lpp_checked_positive_receipt_sound[OF compatible _ Cons.prems(2)])
      (use Cons.prems(1) in simp)
  have tail: "list_all (lpp_stable_observation_holds operation eta)
    ((observations@[lpp_positive_conclusion receipt])@map lpp_positive_conclusion receipts)"
    by (rule Cons.IH) (use Cons.prems step in simp_all)
  then show ?case by simp
qed

definition lpp_positive_context where
  "lpp_positive_context context receipts =
    (fst context, fst (snd context),
      snd (snd context) @ map lpp_positive_conclusion receipts)"

theorem lpp_positive_context_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_positive_derivation (snd (snd context)) receipts"
    and observed: "lpp_stable_context_holds operation P context eta"
  shows "lpp_stable_context_holds operation P (lpp_positive_context context receipts) eta"
proof -
  obtain facts guards observations where shape: "context=(facts,guards,observations)"
    by (cases "context") auto
  have initial: "list_all (lpp_stable_observation_holds operation eta) observations"
    using observed by (simp add: shape lpp_stable_context_holds_def)
  have complete: "list_all (lpp_stable_observation_holds operation eta)
    (observations @ map lpp_positive_conclusion receipts)"
    by (rule lpp_checked_positive_derivation_sound[OF compatible _ initial])
      (use checked in \<open>simp add: shape\<close>)
  show ?thesis using observed complete lpp_stable_observation_refines
    by (auto simp: shape lpp_positive_context_def lpp_stable_context_holds_def
      lpp_evaluation_context_holds_def list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_checked_positive_receipt_sound},
  @{thm lpp_checked_positive_derivation_sound}, @{thm lpp_positive_context_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted positive context dependency" else ();
\<close>
end
