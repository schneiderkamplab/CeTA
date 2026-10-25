theory LP_Cut_Projected_Residual_Regression
  imports LP_Cut_Projected_Residual
begin

text \<open>The list element is arbitrary, including an unbound variable or an
infinite rational tree. Only the finite tail projection is needed. The symbols
are parameters, not names recognized by the checker.\<close>

lemma lpc_spine_discards_arbitrary_element:
  fixes pi :: "'f afs"
  assumes tail_filter: "afs pi (cons,2) = AFList [1]"
    and tail_projection: "lp_iproject pi tail spine"
  shows "lp_iproject pi (LPIFun cons [element,tail]) (Fun cons [spine])"
  by (rule lp_iproject.list[where indices="[1]"])
    (use tail_filter tail_projection in \<open>auto simp: numeral_2_eq_2\<close>)

lemma lpc_unbound_spine_is_not_finite:
  fixes pi :: "'f afs"
  shows "\<not>lp_iproject pi (LPIVar x) spine"
  by (auto elim: lp_iproject.cases)

lemma lpc_retained_unbound_element_is_rejected:
  fixes pi :: "'f afs"
    and spine :: "('f,'v) term"
  assumes keep: "afs pi (cons,2) = AFList [0,1]"
  shows "\<not>lp_iproject pi (LPIFun cons [LPIVar x,tail]) spine"
proof
  assume pr: "lp_iproject pi (LPIFun cons [LPIVar x,tail]) spine"
  have "\<exists>u::('f,'v) term. lp_iproject pi (LPIVar x) u"
    using pr keep
    by (cases rule: lp_iproject.cases)
      (auto simp: numeral_2_eq_2 list_all2_Cons1)
  then obtain u :: "('f,'v) term" where impossible: "lp_iproject pi (LPIVar x) u"
    by (rule exE)
  from impossible show False by (cases rule: lp_iproject.cases)
qed

lemma lpc_projected_edge_refresh_positive:
  "lpc_check_projected_edge 100 2 [] [''X''] []
    (Var ''X'' :: (string,string) term) (Var ''$$X'')
    (Var ''$$X'') (Var ''$$X'')"
  by eval

lemma lpc_projected_edge_stale_namespace_negative:
  "\<not>lpc_check_projected_edge 100 2 [] [''X''] []
    (Var ''X'' :: (string,string) term) (Var ''$$X'')
    (Var ''X'') (Var ''$$X'')"
  by eval

lemma lpc_projected_edge_saved_namespace_negative:
  "\<not>lpc_check_projected_edge 100 2 [] [] []
    (Var ''X'' :: (string,string) term) (Var ''X'')
    (Var ''$$X'') (Var ''X'')"
  by eval

end
