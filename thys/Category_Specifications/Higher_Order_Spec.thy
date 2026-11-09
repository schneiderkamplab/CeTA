theory Higher_Order_Spec
  imports Higher_Order_Spec_Base
begin
text \<open>The signature is a finite list of constant types. Rules are finite
and obey the typed pattern restrictions of the higher-order category. Free names are natural numbers;
each finite typing environment gives the types of the names it admits.\<close>
definition higher_order_problem where
  "higher_order_problem S R \<longleftrightarrow> list_all (higher_category_rule S) R"

text \<open>At a fixed type and free-variable environment, a step is a rule
instance or beta contraction in an arbitrary application or abstraction context.
Both endpoints must have that type. Meta-arguments are instantiated explicitly;
this is not matching modulo unrestricted beta or eta conversion.\<close>
definition higher_order_step where
  "higher_order_step S V R A t u \<longleftrightarrow>
    higher_typeof S V [] t = Some A \<and> higher_typeof S V [] u = Some A \<and>
    higher_step S V R [] t u"

end
