theory LP_Return_Shape_Projection_Test
 imports LP_Return_Shape_Projection LP_Return_Shapes_Test
begin

lemma lprs_spine_filter_accepts:
  fixes flt :: "nat afs"
  assumes nil: "Argument_Filter.afs flt (0,0)=AFList []"
    and cons: "Argument_Filter.afs flt (1,2)=AFList [1]"
  shows "lp_return_shape_filter_check flt id lprs_spine"
  using nil cons by (simp add: lp_return_shape_filter_check_def lprs_spine_def eval_nat_numeral)

lemma lprs_spine_filter_rejects_unobserved_head:
  fixes flt :: "nat afs"
  assumes "Argument_Filter.afs flt (1,2)=AFList [0,1]"
  shows "\<not>lp_return_shape_filter_check flt id lprs_spine"
  using assms by (simp add: lp_return_shape_filter_check_def lprs_spine_def eval_nat_numeral)

lemma lprs_spine_filter_rejects_head_collapse:
  fixes flt :: "nat afs"
  assumes "Argument_Filter.afs flt (1,2)=Collapse 0"
  shows "\<not>lp_return_shape_filter_check flt id lprs_spine"
  using assms by (simp add: lp_return_shape_filter_check_def lprs_spine_def eval_nat_numeral)

lemma lprs_projected_spine_allows_arbitrary_head:
  fixes flt :: "nat afs" and h :: "(nat,string) lp_iterm"
  assumes "Argument_Filter.afs flt (0,0)=AFList []"
    and "Argument_Filter.afs flt (1,2)=AFList [1]"
  shows "\<exists>u::(nat,string) term. lp_iproject flt (LPIFun 1 [h,LPIFun 0 []]) u"
  using lp_return_shape_filter_projection[where data=id,
    OF lprs_spine_filter_accepts[OF assms] lprs_arbitrary_head]
  by (simp add: lp_observed_map_identity)

text \<open>The arbitrary head includes rational cycles. The existing
lprs_cyclic_spine_rejected theorem rules out cycles in the observed tail itself.\<close>
end
