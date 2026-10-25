theory LP_Cut_SEG_Triple_Receipt_Test
  imports LP_Cut_SEG_Triple_Split
begin

abbreviation h :: "(nat,nat) lp_atom" where "h \<equiv> (0,[Var 0])"
abbreviation p :: "(nat,nat) lp_atom" where "p \<equiv> (1,[Var 0])"
abbreviation b :: "(nat,nat) lp_atom" where "b \<equiv> (2,[Var 0])"

lemma answer_clause_positive:
  "lpc_triple_check_model_clause [(h,[p])] [p] h 0 [(0,Var 0)]"
  by (simp add: lpc_triple_check_model_clause_def lp_atom_subst_def lpc_triple_model_subst_def)

lemma omitted_successful_prefix_rejected:
  "\<not> lpc_triple_check_model_clause [(h,[p])] [] h 0 [(0,Var 0)]"
  by (simp add: lpc_triple_check_model_clause_def lp_atom_subst_def lpc_triple_model_subst_def)

lemma unrelated_answer_environment_rejected:
  "\<not> lpc_triple_check_model_clause [(h,[p])] [(1,[Var 1])] h 0 [(0,Var 0)]"
  by (simp add: lpc_triple_check_model_clause_def lp_atom_subst_def lpc_triple_model_subst_def)

lemma conditional_call_positive:
  "lpc_triple_check_call [(h,[p],b)] [p] h b 0 [(0,Var 0)]"
  by (simp add: lpc_triple_check_call_def lp_atom_subst_def lpc_triple_model_subst_def)

lemma unconditional_promotion_rejected:
  "\<not> lpc_triple_check_call [(h,[p],b)] [] h b 0 [(0,Var 0)]"
  by (simp add: lpc_triple_check_call_def lp_atom_subst_def lpc_triple_model_subst_def)

lemma wrong_call_rejected:
  "\<not> lpc_triple_check_call [(h,[p],b)] [p] h (2,[Var 1]) 0 [(0,Var 0)]"
  by (simp add: lpc_triple_check_call_def lp_atom_subst_def lpc_triple_model_subst_def)

lemma missing_call_rejected:
  "\<not> lpc_triple_check_call [] [p] h b 0 []"
  by (simp add: lpc_triple_check_call_def)

end
