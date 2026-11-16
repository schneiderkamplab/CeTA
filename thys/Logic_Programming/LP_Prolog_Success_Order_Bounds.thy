theory LP_Prolog_Success_Order_Bounds
  imports LP_Prolog_Success_Magnitude_Program LP_Prolog_Evaluated_Integer_Expressions
begin

text \<open>Order contracts concern actual successful derivations. Their input
premise is integer evaluation of a source expression, not literal integer
membership of the expression itself. Both increasing and decreasing helper
families use the same checked bound language.\<close>

definition lpp_order_relation where
  "lpp_order_relation increasing n m = (if increasing then n\<le>m else m\<le>n)"

datatype lpp_order_bound = LPPOrderKnown nat | LPPOrderShift lpp_order_bound int | LPPOrderSubtract lpp_order_bound int

fun lpp_check_order_bound where
  "lpp_check_order_bound increasing known t (LPPOrderKnown i) =
    (i<length known \<and> known!i=t)"
| "lpp_check_order_bound increasing known t (LPPOrderShift p k) =
    (lpp_order_relation increasing 0 k \<and>
      (case t of Fun f [a,b] \<Rightarrow> f=LPCUser ''2:prolog_data_2b'' \<and>
        b=lpp_integer_term k \<and> lpp_check_order_bound increasing known a p
       | _ \<Rightarrow> False))"

| "lpp_check_order_bound increasing known t (LPPOrderSubtract p k) =
    (lpp_order_relation increasing k 0 \<and>
      (case t of Fun f [a,b] \<Rightarrow> f=LPCUser ''2:prolog_data_2d'' \<and>
        b=lpp_integer_term k \<and> lpp_check_order_bound increasing known a p
       | _ \<Rightarrow> False))"

definition lpp_order_bound_holds where
  "lpp_order_bound_holds operation increasing eta n t =
    (\<exists>m. lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value m) \<and>
      lpp_order_relation increasing n m)"

lemma lpp_check_order_bound_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_order_bound increasing known t receipt"
    and known: "\<And>v. v\<in>set known \<Longrightarrow> lpp_order_bound_holds operation increasing eta n v"
  shows "lpp_order_bound_holds operation increasing eta n t"
  using checked known
proof (induction receipt arbitrary: t)
  case (LPPOrderKnown i)
  then have "t\<in>set known" by (auto intro: nth_mem)
  then show ?case by (rule known)
next
  case (LPPOrderShift receipt k)
  obtain a where shape: "t=Fun (LPCUser ''2:prolog_data_2b'') [a,lpp_integer_term k]"
    and checked: "lpp_check_order_bound increasing known a receipt"
    and shift: "lpp_order_relation increasing 0 k"
    using LPPOrderShift.prems(1) by (auto split: term.splits list.splits)
  obtain m where evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval a eta) (lpp_integer_value m)"
    and ordered: "lpp_order_relation increasing n m"
    using LPPOrderShift.IH[OF checked known] by (auto simp: lpp_order_bound_holds_def)
  have result: "lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value (m+k))"
    using evaluated compatible unfolding shape lpp_stable_integer_operations_def
      by (auto intro: lpp_stable_scalar_evaluation.intros lpp_stable_integer_literal lpp_integer_scalar_observation)
  have order: "lpp_order_relation increasing n (m+k)"
    using shift ordered by (auto simp: lpp_order_relation_def)
  show ?case using result order by (auto simp: lpp_order_bound_holds_def)
next
  case (LPPOrderSubtract receipt k)
  obtain a where shape: "t=Fun (LPCUser ''2:prolog_data_2d'') [a,lpp_integer_term k]"
    and checked: "lpp_check_order_bound increasing known a receipt"
    and shift: "lpp_order_relation increasing k 0"
    using LPPOrderSubtract.prems(1) by (auto split: term.splits list.splits)
  obtain m where evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval a eta) (lpp_integer_value m)"
    and ordered: "lpp_order_relation increasing n m"
    using LPPOrderSubtract.IH[OF checked known] by (auto simp: lpp_order_bound_holds_def)
  have result: "lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value (m-k))"
    using evaluated compatible unfolding shape lpp_stable_integer_operations_def
      by (auto intro: lpp_stable_scalar_evaluation.intros lpp_stable_integer_literal lpp_integer_scalar_observation)
  have order: "lpp_order_relation increasing n (m-k)"
    using shift ordered by (auto simp: lpp_order_relation_def)
  show ?case using result order by (auto simp: lpp_order_bound_holds_def)
qed

lemma lpp_order_evaluation_return:
  assumes compatible: "lpp_stable_integer_operations operation"
    and bound: "lpp_order_bound_holds operation increasing eta n expression"
    and returned: "lpp_stable_scalar_evaluation operation (lp_ieval expression eta) result"
  shows "\<exists>m. result=lpp_integer_value m \<and> lpp_order_relation increasing n m"
proof -
  obtain m where evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval expression eta) (lpp_integer_value m)"
    and order: "lpp_order_relation increasing n m"
    using bound by (auto simp: lpp_order_bound_holds_def)
  have "result=lpp_integer_value m"
    using lpp_stable_scalar_evaluation_unique[OF returned evaluated] by blast
  then show ?thesis using order by blast
qed

ML \<open>
val checked = [@{thm lpp_check_order_bound_sound}, @{thm lpp_order_evaluation_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted conditional return order dependency" else ();
\<close>
end
