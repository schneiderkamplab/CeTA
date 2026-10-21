theory LP_Mode_Regression
  imports LP_Mode_Checker
begin

lemma mode_cover_cannot_replace_recursion_by_fact:
  "\<not> lp_check_mode_cover
    ([((0,[]),[(0,[])])] :: (nat,nat) lp_clause list)
    [((1,[]),[])] [(1,0)]"
  by (simp add: lp_check_mode_cover_def lp_mode_clause_def lp_mode_atom_def)

lemma mode_cover_cannot_omit_alternative:
  "\<not> lp_check_mode_cover
    ([((0,[]),[]),((0,[]),[(0,[])])] :: (nat,nat) lp_clause list)
    [((1,[]),[])] [(1,0)]"
  by (simp add: lp_check_mode_cover_def lp_mode_clause_def lp_mode_atom_def)

lemma mode_cover_accepts_distinct_call_copies:
  "lp_check_mode_cover
    ([((0,[]),[(2,[]),(2,[])]),((2,[]),[])] :: (nat,nat) lp_clause list)
    [((1,[]),[(3,[]),(4,[])]),((3,[]),[]),((4,[]),[])] [(1,0),(3,2),(4,2)]"
  by (simp add: lp_check_mode_cover_def lp_mode_clause_def lp_mode_atom_def)

lemma mode_cover_cannot_change_data:
  "\<not> lp_check_mode_cover
    ([((0,[Fun 7 []]),[])] :: (nat,nat) lp_clause list)
    [((1,[Fun 8 []]),[])] [(1,0)]"
  by (simp add: lp_check_mode_cover_def lp_mode_clause_def lp_mode_atom_def)

end
