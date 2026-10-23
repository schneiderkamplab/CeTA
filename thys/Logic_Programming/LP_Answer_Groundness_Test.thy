theory LP_Answer_Groundness_Test
  imports LP_Answer_Groundness
begin

definition ground_test_minus :: "(string,string) lp_clause list" where
  "ground_test_minus = [
    ((''minus'',[Fun ''zero'' [],Var ''Y'',Fun ''zero'' []]),[]),
    ((''minus'',[Var ''X'',Fun ''zero'' [],Var ''X'']),[]),
    ((''minus'',[Fun ''succ'' [Var ''X''],Fun ''succ'' [Var ''Y''],Var ''Z'']),
      [(''minus'',[Var ''X'',Var ''Y'',Var ''Z''])])]"

lemma recursive_output_groundness:
  "lp_ground_check ground_test_minus [LPGroundMode ''minus'' 3 [0,1] [0,1,2]]"
  by eval

lemma insufficient_input_rejected:
  "\<not> lp_ground_check ground_test_minus [LPGroundMode ''minus'' 3 [1] [2]]"
  by eval

lemma missing_recursive_contract_rejected:
  "\<not> lp_ground_check
    [((''p'',[Var ''X'',Var ''Y'']),[(''q'',[Var ''X'',Var ''Y''])])]
    [LPGroundMode ''p'' 2 [0] [1]]"
  by eval

lemma unbound_fact_rejected:
  "\<not> lp_ground_check [((''p'',[Var ''X'',Var ''Y'']),[])]
    [LPGroundMode ''p'' 2 [0] [1]]"
  by eval

lemma invalid_position_rejected:
  "\<not> lp_ground_check ground_test_minus [LPGroundMode ''minus'' 3 [0,1] [3]]"
  by eval

lemma rational_cycle_not_finite_ground:
  "\<not> lp_ground_check
    [((''p'',[Var ''X'']),[(''eq'',[Var ''X'',Fun ''f'' [Var ''X'']])]),
     ((''eq'',[Var ''X'',Var ''X'']),[])]
    [LPGroundMode ''p'' 1 [] [0], LPGroundMode ''eq'' 2 [] [0,1]]"
  by eval

lemma mutual_recursion_validated:
  "lp_ground_check
    [((''p'',[Var ''X'',Var ''Y'']),[(''q'',[Var ''X'',Var ''Y''])]),
     ((''q'',[Var ''X'',Var ''Y'']),[(''p'',[Var ''X'',Var ''Y''])]),
     ((''q'',[Var ''X'',Var ''X'']),[])]
    [LPGroundMode ''p'' 2 [0] [0,1], LPGroundMode ''q'' 2 [0] [0,1]]"
  by eval

text \<open>The last example need not terminate. Its contract concerns only
finite successful derivations and therefore does not assume termination.\<close>

end
