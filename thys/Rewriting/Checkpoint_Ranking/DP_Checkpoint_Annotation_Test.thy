theory DP_Checkpoint_Annotation_Test
 imports DP_Checkpoint_Annotation
begin

lemma checkpoint_annotation_coordinate_bounds:
 "\<not>checkpoint_atom_bounded n (CP_Exact n)"
 "\<not>checkpoint_atom_bounded n (CP_Ground f 0 n)"
 "\<not>checkpoint_atom_bounded n (CP_List f n 0)"
 by (simp_all add: checkpoint_atom_bounded_def)

lemma checkpoint_annotation_wrong_arity:
 "\<not>checkpoint_annotation_holds C L N Z S R [(f,Suc (length ts),clause)] old (Fun f ts)"
 by (simp add: checkpoint_annotation_holds_def)

lemma checkpoint_pending_not_success:
 "checkpoint_pending_ground C {} f (Fun f [Var (0::nat)]) (Var (0::nat))"
 "\<not>checkpoint_guard C L (Var (0::nat))"
 unfolding checkpoint_pending_ground_def checkpoint_guard_def
 by (auto intro!: exI[of _ "Var (0::nat)"])

lemma checkpoint_alternatives_do_not_merge:
 "checkpoint_annotation_holds ({}::nat set) 0 1 2 3 {}
 [(4,2,[CP_Exact 0]),(4,2,[CP_Guard 1])] [] (Fun 4 [Var (0::nat),Var 1])"
 "\<not>checkpoint_clause_holds ({}::nat set) 0 1 2 3 {} []
 [CP_Exact 0,CP_Guard 1] [Var (0::nat),Var 1]"
 by (simp_all add: checkpoint_annotation_holds_def checkpoint_clause_holds_def checkpoint_atom_bounded_def checkpoint_guard_def)

ML \<open>
val thms = @{thms checkpoint_annotation_coordinate_bounds checkpoint_annotation_wrong_arity checkpoint_pending_not_success checkpoint_alternatives_do_not_merge};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted annotation controls" else ();
\<close>
end
