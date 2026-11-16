theory LP_Prolog_Success_Order_Contracts
  imports LP_Prolog_Success_Order_Bounds LP_Prolog_Numeric_Return_Calls
begin

datatype lpp_order_base = LPPOrderArgument nat | LPPOrderConstant int

fun lpp_order_base_select where
  "lpp_order_base_select literal ts (LPPOrderArgument i) =
    (if i<length ts then Some (ts!i) else None)"
| "lpp_order_base_select literal ts (LPPOrderConstant k) = Some (literal k)"

lemma lpp_order_base_select_map:
  "lpp_order_base_select (f o literal) (map f ts) selector =
    map_option f (lpp_order_base_select literal ts selector)"
  by (cases selector) simp_all

type_synonym lpp_order_summaries =
  "(string \<times> nat) \<Rightarrow> (bool \<times> lpp_order_base \<times> nat) list"

definition lpp_order_contract_holds where
  "lpp_order_contract_holds operation ts contract = (case contract of (increasing,selector,j) \<Rightarrow>
    j<length ts \<and> (case lpp_order_base_select lpp_integer_value ts selector of
      None \<Rightarrow> False
    | Some t \<Rightarrow> (\<forall>n. lpp_stable_scalar_evaluation operation t (lpp_integer_value n) \<longrightarrow>
        (\<exists>m. ts!j=lpp_integer_value m \<and> lpp_order_relation increasing n m))))"

definition lpp_order_summaries_hold where
  "lpp_order_summaries_hold operation summaries a =
    list_all (lpp_order_contract_holds operation (snd a)) (summaries (fst a,length (snd a)))"

datatype 'v lpp_order_fact =
    LPPOrderEvaluation nat lpp_order_bound 'v
  | LPPOrderHelper nat nat lpp_order_bound 'v
  | LPPOrderComparedEvaluation nat nat lpp_order_bound 'v

fun lpp_order_fact_variable where
  "lpp_order_fact_variable (LPPOrderEvaluation i p x) = x"
| "lpp_order_fact_variable (LPPOrderHelper i r p x) = x"
| "lpp_order_fact_variable (LPPOrderComparedEvaluation i j p x) = x"

fun lpp_order_comparison_terms where
 "lpp_order_comparison_terms increasing (LPPSNumeric c a b) =
   (if c=0 \<or> c=1 then Some (if increasing then (a,b) else (b,a)) else None)"
| "lpp_order_comparison_terms increasing g = None"



lemma lpp_order_comparison_terms_sound:
 assumes terms: "lpp_order_comparison_terms increasing g=Some (b,e)"
   and guard: "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta g"
   and base: "lpp_stable_scalar_evaluation operation (lp_ieval b eta) (lpp_integer_value k)"
   and target: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (lpp_integer_value m)"
 shows "lpp_order_relation increasing k m"
proof (cases increasing)
 case True
 obtain c where shape: "g=LPPSNumeric c b e" "c=0 \<or> c=1"
   using terms True by (cases g) (auto split: if_splits)
 have relation: "lpp_success_numeric_relation c k m"
   by (rule lpp_success_numeric_guard_integer_relation[OF guard[unfolded shape(1)] base target])
 show ?thesis using relation shape(2) True by (auto simp: lpp_order_relation_def)
next
 case False
 obtain c where shape: "g=LPPSNumeric c e b" "c=0 \<or> c=1"
   using terms False by (cases g) (auto split: if_splits)
 have relation: "lpp_success_numeric_relation c m k"
   by (rule lpp_success_numeric_guard_integer_relation[OF guard[unfolded shape(1)] target base])
 show ?thesis using relation shape(2) False by (auto simp: lpp_order_relation_def)
qed

fun lpp_check_order_fact where
  "lpp_check_order_fact summaries increasing bs gs known (LPPOrderEvaluation i p x) =
    (i<length gs \<and> (case gs!i of LPPSEvaluates expression result \<Rightarrow>
      result=Var x \<and> lpp_check_order_bound increasing known expression p
      | _ \<Rightarrow> False))"
| "lpp_check_order_fact summaries increasing bs gs known (LPPOrderHelper i r p x) =
    (i<length bs \<and> r<length (summaries (fst (bs!i),length (snd (bs!i)))) \<and>
     (case summaries (fst (bs!i),length (snd (bs!i)))!r of (direction,selector,j) \<Rightarrow>
       direction=increasing \<and> j<length (snd (bs!i)) \<and> snd (bs!i)!j=Var x \<and>
       (case lpp_order_base_select lpp_integer_term (snd (bs!i)) selector of
         None \<Rightarrow> False | Some t \<Rightarrow> lpp_check_order_bound increasing known t p)))"

| "lpp_check_order_fact summaries increasing bs gs known (LPPOrderComparedEvaluation i j p x) =
    (i<length gs \<and> j<length gs \<and> (case gs!i of LPPSEvaluates e result \<Rightarrow>
      result=Var x \<and> e\<in>set (concat (map lpp_success_evaluated_integers gs)) \<and>
      (case lpp_order_comparison_terms increasing (gs!j) of None \<Rightarrow> False
       | Some (b,t) \<Rightarrow> t=e \<and> lpp_check_order_bound increasing known b p)
      | _ \<Rightarrow> False))"

lemma lpp_order_contract_apply:
  assumes contract: "lpp_order_contract_holds operation (map (\<lambda>t. lp_ieval t eta) ts) (increasing,selector,j)"
    and selected: "lpp_order_base_select lpp_integer_term ts selector=Some t"
    and bound: "lpp_order_bound_holds operation increasing eta n t"
  shows "\<exists>m. lp_ieval (ts!j) eta=lpp_integer_value m \<and> lpp_order_relation increasing n m"
proof -
  have selection: "lpp_order_base_select lpp_integer_value (map (\<lambda>t. lp_ieval t eta) ts) selector = Some (lp_ieval t eta)"
    using lpp_order_base_select_map[of "\<lambda>t. lp_ieval t eta" lpp_integer_term ts selector] selected
    by (simp add: o_def)
  obtain k where input: "lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value k)"
    and first: "lpp_order_relation increasing n k"
    using bound by (auto simp: lpp_order_bound_holds_def)
  obtain m where result: "lp_ieval (ts!j) eta=lpp_integer_value m"
    and second: "lpp_order_relation increasing k m"
    using contract input selection by (auto simp: lpp_order_contract_holds_def)
  have "lpp_order_relation increasing n m"
    using first second by (auto simp: lpp_order_relation_def)
  then show ?thesis using result by blast
qed

lemma lpp_check_order_fact_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_order_fact summaries increasing bs gs known receipt"
    and known: "\<And>t. t\<in>set known \<Longrightarrow> lpp_order_bound_holds operation increasing eta n t"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_order_summaries_hold operation summaries (lpp_success_atom_eval b eta)) bs"
  shows "\<exists>m. eta (lpp_order_fact_variable receipt)=lpp_integer_value m \<and>
    lpp_order_relation increasing n m"
proof (cases receipt)
  case (LPPOrderEvaluation i p x)
  obtain expression where index: "i<length gs" and shape: "gs!i=LPPSEvaluates expression (Var x)"
    and bound: "lpp_check_order_bound increasing known expression p"
    using checked LPPOrderEvaluation by (auto split: lpp_success_guard.splits)
  have observation: "lpp_stable_scalar_evaluation operation (lp_ieval expression eta) (eta x)"
    using guards index shape by (auto simp: list_all_length)
  have evaluated: "lpp_order_bound_holds operation increasing eta n expression"
    by (rule lpp_check_order_bound_sound[OF compatible bound known])
  show ?thesis using lpp_order_evaluation_return[OF compatible evaluated observation]
    by (simp add: LPPOrderEvaluation)
next
  case (LPPOrderHelper i r p x)
  obtain selector j t where index: "i<length bs"
    and rule_index: "r<length (summaries (fst (bs!i),length (snd (bs!i))))"
    and rule: "summaries (fst (bs!i),length (snd (bs!i)))!r=(increasing,selector,j)"
    and outpos: "j<length (snd (bs!i))" "snd (bs!i)!j=Var x"
    and selected: "lpp_order_base_select lpp_integer_term (snd (bs!i)) selector=Some t"
    and bound: "lpp_check_order_bound increasing known t p"
    using checked LPPOrderHelper by (auto split: prod.splits option.splits)
  have all: "lpp_order_summaries_hold operation summaries (lpp_success_atom_eval (bs!i) eta)"
    using helpers index by (simp add: list_all_length)
  have contract: "lpp_order_contract_holds operation (map (\<lambda>t. lp_ieval t eta) (snd (bs!i))) (increasing,selector,j)"
    using all rule_index rule
    by (auto simp: lpp_order_summaries_hold_def lpp_success_atom_eval_def list_all_length)
  have evaluated: "lpp_order_bound_holds operation increasing eta n t"
    by (rule lpp_check_order_bound_sound[OF compatible bound known])
  show ?thesis using lpp_order_contract_apply[OF contract selected evaluated] outpos
    by (simp add: LPPOrderHelper)
next
 case (LPPOrderComparedEvaluation i j p x)
 obtain e b where indices: "i<length gs" "j<length gs"
   and evaluation: "gs!i=LPPSEvaluates e (Var x)"
   and typing: "e\<in>set (concat (map lpp_success_evaluated_integers gs))"
   and terms: "lpp_order_comparison_terms increasing (gs!j)=Some (b,e)"
   and bound: "lpp_check_order_bound increasing known b p"
   using checked LPPOrderComparedEvaluation by (auto split: lpp_success_guard.splits option.splits prod.splits)
 obtain g where member: "g\<in>set gs" and selected: "e\<in>set (lpp_success_evaluated_integers g)"
   using typing by auto
 have held: "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta g"
   using guards member by (simp add: list_all_iff)
 obtain m where integer: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (lpp_integer_value m)"
   using lpp_success_evaluated_integers_sound[OF compatible held selected] by blast
 obtain k where base: "lpp_stable_scalar_evaluation operation (lp_ieval b eta) (lpp_integer_value k)"
   and first: "lpp_order_relation increasing n k"
   using lpp_check_order_bound_sound[OF compatible bound known] by (auto simp: lpp_order_bound_holds_def)
 have comparison: "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta (gs!j)"
   using guards indices by (simp add: list_all_length)
 have second: "lpp_order_relation increasing k m"
   by (rule lpp_order_comparison_terms_sound[OF terms comparison base integer])
 have ordered: "lpp_order_relation increasing n m"
   using first second by (auto simp: lpp_order_relation_def)
 have evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (eta x)"
   using guards indices evaluation by (auto simp: list_all_length)
 have returned_value: "eta x=lpp_integer_value m"
   by (rule lpp_stable_scalar_evaluation_unique[OF evaluated integer])
 show ?thesis using returned_value ordered by (simp add: LPPOrderComparedEvaluation)

qed

ML \<open>
val checked = [@{thm lpp_order_contract_apply}, @{thm lpp_check_order_fact_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted conditional order fact dependency" else ();
\<close>
end
