theory Higher_Order_Sorts_Spec
  imports Higher_Order_Spec
begin
text \<open>An ARI input declares finitely many base sorts, numbered below N.
Only these sorts occur in variable types, result types and binder annotations.\<close>
fun higher_sort_type where
  "higher_sort_type N (SpecHBase n) = (n < N)"
| "higher_sort_type N (SpecHArrow A B) = (higher_sort_type N A \<and> higher_sort_type N B)"
fun higher_sort_term where
  "higher_sort_term N (SpecHAbs A t) = (higher_sort_type N A \<and> higher_sort_term N t)"
| "higher_sort_term N (SpecHApp t u) = (higher_sort_term N t \<and> higher_sort_term N u)"
| "higher_sort_term N t = True"
fun higher_sort_pattern where
  "higher_sort_pattern N (SpecPAbs A t) = (higher_sort_type N A \<and> higher_sort_pattern N t)"
| "higher_sort_pattern N (SpecPApp t u) = (higher_sort_pattern N t \<and> higher_sort_pattern N u)"
| "higher_sort_pattern N (SpecPMeta n ps) = list_all (higher_sort_pattern N) ps"
| "higher_sort_pattern N p = True"
definition higher_sort_rule where
  "higher_sort_rule N r \<longleftrightarrow> (case r of (G,l,u) \<Rightarrow>
    list_all (higher_sort_type N) G \<and> higher_sort_pattern N l \<and> higher_sort_pattern N u)"
text \<open>Category validity includes all declared types. With no base sorts,
there are no typed rules. This explicit empty case also avoids inventing a sort.\<close>
definition higher_order_declared_problem where
  "higher_order_declared_problem N S R \<longleftrightarrow> higher_order_problem S R \<and>
    list_all (higher_sort_type N) S \<and> list_all (higher_sort_rule N) R \<and> (N = 0 \<longrightarrow> R = [])"
definition higher_order_terminates_over_sorts where
  "higher_order_terminates_over_sorts N S R \<longleftrightarrow>
    (\<forall>V A. list_all (higher_sort_type N) V \<and> higher_sort_type N A \<longrightarrow>
      no_infinite_steps (\<lambda>t u. higher_sort_term N t \<and> higher_sort_term N u \<and>
        higher_order_step S V R A t u))"
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
