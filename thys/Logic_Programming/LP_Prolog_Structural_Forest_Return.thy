theory LP_Prolog_Structural_Forest_Return
 imports LP_Prolog_Structural_Return_Contracts LP_Prolog_Forest_Return_Order
begin

text \<open>Connect authenticated successful-return facts to the shared forest
order. The input head and tail and the actual output tail can be any checked
coordinates. This theorem neither authenticates those coordinates nor proves
the helper's termination.\<close>

lemma lpp_structural_return_forest_descent:
 assumes head: "lpp_structural_return_holds replacement_sets value (LPPRTree head_coordinate)"
 and spine: "lpp_structural_return_holds replacement_sets value (LPPRSpine before_coordinate)"
 and effect: "lpp_structural_return_holds replacement_sets value
   (LPPRLeafEffect before_coordinate after_coordinate replacements)"
 and ground: "lpp_structural_return_holds replacement_sets value (LPPRLeafFreeReplacements replacements)"
 shows "\<exists>head_shape xs ys.
   lpp_runtime_structure (value head_coordinate) head_shape \<and>
   lpp_runtime_structure (value before_coordinate) (lpp_structural_argument_list xs) \<and>
   lpp_runtime_structure (value after_coordinate) (lpp_structural_argument_list ys) \<and>
   ((Inr ys :: (string lp_cut_symbol+unit,unit) term + (string lp_cut_symbol+unit,unit) term list),Inr (head_shape#xs))\<in>lpp_forest_call_order"
proof -
 obtain head_shape where observed_head: "lpp_runtime_structure (value head_coordinate) head_shape"
  using head lpp_runtime_structure_exists by auto
 obtain initial where observed_tail: "lpp_runtime_structure (value before_coordinate) initial"
 and returned: "lpp_runtime_leaf_effect (replacement_sets replacements) initial (value after_coordinate)"
  using effect by auto
 obtain n where length: "lpp_list_length (value before_coordinate) n" using spine by auto
 have finite: "lpp_finite_term (value before_coordinate)"
  by (rule lpp_runtime_structure_finite[OF observed_tail])
 obtain xs where list_before: "lpp_runtime_structure (value before_coordinate) (lpp_structural_argument_list xs)"
  using lpp_finite_spine_structural_observation[OF length finite] by blast
 have shape: "initial=lpp_structural_argument_list xs"
  by (rule lpp_runtime_structure_unique[OF observed_tail list_before])
 have leaf_free: "vars_term u = {}" if "u\<in>replacement_sets replacements" for u
  using ground that by simp
 obtain ys where list_after: "lpp_runtime_structure (value after_coordinate) (lpp_structural_argument_list ys)"
 and decrease: "((Inr ys :: (string lp_cut_symbol+unit,unit) term + (string lp_cut_symbol+unit,unit) term list),Inr (head_shape#xs))\<in>lpp_forest_call_order"
  using lpp_runtime_returned_argument_tail_decreases[OF returned[unfolded shape] leaf_free observed_head] by blast
 show ?thesis
  by (rule exI[of _ head_shape], rule exI[of _ xs], rule exI[of _ ys])
     (use observed_head list_before list_after decrease in auto)
qed

ML \<open>
val checked = @{thms lpp_structural_return_forest_descent};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted structural forest return" else ();
\<close>
end
