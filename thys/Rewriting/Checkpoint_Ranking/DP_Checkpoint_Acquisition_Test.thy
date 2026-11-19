theory DP_Checkpoint_Acquisition_Test
 imports DP_Checkpoint_Acquisition
begin

definition acquisition_before :: "(nat,nat) rule" where
 "acquisition_before=(Fun 0 [Var 0],Fun 1 [Var 0,Fun 2 [Var 0]])"
definition acquisition_after :: "(nat,nat) rule" where
 "acquisition_after=(Fun 1 [Var 0,Fun 3 [Var 0,Var 1]],Fun 4 [Var 1])"
lemma acquisition_position_checked:
 "check_checkpoint_acquisition {0,1,4} 1 2 1 3 2 acquisition_before acquisition_after"
 by (simp add: acquisition_before_def acquisition_after_def)
lemma acquisition_wrong_coordinate_rejected:
 "\<not>check_checkpoint_acquisition {0,1,4} 0 2 1 3 2 acquisition_before acquisition_after"
 "\<not>check_checkpoint_acquisition {0,1,4} 2 2 1 3 2 acquisition_before acquisition_after"
 by (simp_all add: acquisition_before_def acquisition_after_def)
lemma acquisition_missing_control_rejected:
 "\<not>check_checkpoint_acquisition {0,4} 1 2 1 3 2 acquisition_before acquisition_after"
 by (simp add: acquisition_before_def acquisition_after_def)
lemma acquisition_wrong_output_arity_rejected:
 "\<not>check_checkpoint_acquisition {0,1,4} 1 2 1 3 1 acquisition_before acquisition_after"
 by (simp add: acquisition_before_def acquisition_after_def)
lemma acquisition_wrong_order_rejected:
 "\<not>check_checkpoint_acquisition {0,1,4} 1 2 1 3 2 acquisition_after acquisition_before"
 by (simp add: acquisition_before_def acquisition_after_def)

text \<open>A checked position is not proof that the helper can return.\<close>
lemma acquisition_empty_support_cannot_return:
 "(Fun (2::nat) [x],Fun 3 [y,z])\<notin>(rstep ({}::(nat,nat) trs))\<^sup>*"
 by simp
ML \<open>
val thms = @{thms acquisition_position_checked acquisition_wrong_coordinate_rejected acquisition_missing_control_rejected acquisition_wrong_output_arity_rejected acquisition_wrong_order_rejected acquisition_empty_support_cannot_return};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted acquisition controls" else ();
\<close>
end
