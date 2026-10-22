theory LP_Recurrent_Pair_Tests
  imports LP_Recurrent_Pair_Check
begin

text \<open>A shrinking/rebuilding program with genuinely growing phases:
  p(X,s(Y)) :- p(s(X),Y).  p(X,0) :- p(0,s(X)).
  Numeric symbols are local test fixtures, not processor dispatch.\<close>

definition rp_test_A :: "nat * (nat,nat) term list" where
  "rp_test_A=(0,[Var 0,Var 1])"
definition rp_test_C :: "(nat,nat) term" where
  "rp_test_C=Fun 1 [Var 0]"
definition rp_test_s :: "(nat,nat) term" where
  "rp_test_s=Fun 2 []"
definition rp_test_P :: "(nat,nat) lp_clause list" where
  "rp_test_P=[((0,[Var 0,Fun 1 [Var 1]]),[(0,[Fun 1 [Var 0],Var 1])]),
              ((0,[Var 0,Fun 2 []]),[(0,[Fun 2 [],Fun 1 [Var 0]])])]"

lemma recurrent_pair_positive:
  "lp_recurrent_pair_check rp_test_P 0 2 [0,1] rp_test_A rp_test_C
    0 1 rp_test_s 1 0 0 1 0 1 False [(0,[])] [(1,[])]"
  by eval

lemma recurrent_pair_reject_wrong_phase:
  "\<not>lp_recurrent_pair_check rp_test_P 0 2 [0,1] rp_test_A rp_test_C
    0 1 rp_test_s 1 0 0 1 0 1 False [(1,[])] [(0,[])]"
  by eval

lemma recurrent_pair_reject_empty_phase:
  "\<not>lp_recurrent_pair_check rp_test_P 0 2 [0,1] rp_test_A rp_test_C
    0 1 rp_test_s 1 0 0 1 0 1 False [] [(1,[])]"
  by eval

lemma recurrent_pair_reject_wrong_query:
  "\<not>lp_recurrent_pair_check rp_test_P 3 2 [0,1] rp_test_A rp_test_C
    0 1 rp_test_s 1 0 0 1 0 1 False [(0,[])] [(1,[])]"
  by eval

lemma recurrent_pair_reject_invalid_mode_position:
  "\<not>lp_recurrent_pair_check rp_test_P 0 2 [2] rp_test_A rp_test_C
    0 1 rp_test_s 1 0 0 1 0 1 False [(0,[])] [(1,[])]"
  by eval

lemma recurrent_pair_reject_nonground_seed:
  "\<not>lp_recurrent_pair_check rp_test_P 0 2 [] rp_test_A rp_test_C
    0 1 (Var 2) 1 0 0 1 0 1 False [(0,[])] [(1,[])]"
  by eval

lemma recurrent_pair_reject_aliased_holes:
  "\<not>lp_recurrent_pair_check rp_test_P 0 2 [0,1] rp_test_A rp_test_C
    0 0 rp_test_s 1 0 0 1 0 1 False [(0,[])] [(1,[])]"
  by eval

lemma recurrent_pair_reject_unchecked_context_variable:
  "\<not>lp_recurrent_pair_check rp_test_P 0 2 [0,1] rp_test_A (Fun 1 [Var 2])
    0 1 rp_test_s 1 0 0 1 0 1 False [(0,[])] [(1,[])]"
  by eval

lemma recurrent_pair_reject_phase_bound:
  "\<not>lp_recurrent_pair_check rp_test_P 0 2 [0,1] rp_test_A rp_test_C
    0 1 rp_test_s 1 1 0 1 0 1 False [(0,[])] [(1,[])]"
  by eval

end
