theory Higher_Order_Properties
  imports Category_Specifications.Higher_Order_Spec
    Rewriting_Sequences_Properties
begin

text \<open>Termination quantifies over all finite free-variable environments and
all result types, and excludes every infinite typed rewriting sequence.\<close>
definition higher_order_terminates where
  "higher_order_terminates S R \<longleftrightarrow>
    (\<forall>V A. no_infinite_steps (higher_order_step S V R A))"

lemma higher_order_nontermination_iff:
  "\<not> higher_order_terminates S R \<longleftrightarrow>
    (\<exists>V A ts. \<forall>i. higher_order_step S V R A (ts i) (ts (Suc i)))"
  by (simp add: higher_order_terminates_def no_infinite_steps_def)
end
