theory Higher_Order_Sorts_Properties
  imports Category_Specifications.Higher_Order_Sorts_Spec
    Higher_Order_Properties
begin

lemma higher_order_declared_nontermination_iff:
  "\<not> higher_order_terminates_over_sorts N S R \<longleftrightarrow>
    (\<exists>V A ts. list_all (higher_sort_type N) V \<and> higher_sort_type N A \<and>
      (\<forall>i. higher_sort_term N (ts i) \<and> higher_sort_term N (ts (Suc i)) \<and>
        higher_order_step S V R A (ts i) (ts (Suc i))))"
  by (auto simp: higher_order_terminates_over_sorts_def no_infinite_steps_def)
lemma higher_no_sort_type: "\<not> higher_sort_type 0 A"
  by (induct A) auto
lemma higher_zero_sorts_terminate: "higher_order_terminates_over_sorts 0 S R"
  by (simp add: higher_order_terminates_over_sorts_def higher_no_sort_type)
end
