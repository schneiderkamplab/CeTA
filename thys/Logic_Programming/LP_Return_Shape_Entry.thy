theory LP_Return_Shape_Entry
 imports LP_Return_Shape_Projection
begin

lemma lp_check_query_projectable:
  fixes flt :: "'g afs" and ts :: "('f,'v) lp_iterm list" and data :: "'f \<Rightarrow> 'g"
  assumes query: "lp_check_query flt q n positions" and len: "length ts=n"
    and projectable: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow>
      \<exists>u::('g,'v) term. lp_iproject flt (map_lp_iterm data id (ts!i)) u"
  shows "\<exists>u::('g,'v) term. lp_iproject flt (LPIFun q (map (map_lp_iterm data id) ts)) u"
proof -
  obtain indices where filter: "Argument_Filter.afs flt (q,n)=AFList indices"
    and selected: "set indices \<subseteq> set positions"
    using query unfolding lp_check_query_def
    by (cases "Argument_Filter.afs flt (q,n)") (auto simp: list_all_iff)
  have bounds: "set indices \<subseteq> {0..<n}"
    using Argument_Filter.afs[of n flt q] by (auto simp: filter)
  let ?pick = "\<lambda>i. SOME u::('g,'v) term. lp_iproject flt (map_lp_iterm data id (ts!i)) u"
  have witness: "lp_iproject flt (map_lp_iterm data id (ts!i)) (?pick i)"
    if "i\<in>set indices" for i
    by (rule someI_ex, rule projectable) (use selected bounds that in auto)
  have result: "lp_iproject flt (LPIFun q (map (map_lp_iterm data id) ts)) (Fun q (map ?pick indices))"
    by (rule lp_iproject.list[where indices=indices])
      (use filter len bounds witness in \<open>auto simp: list_all2_map2 list_all2_same list_all_iff\<close>)
  show ?thesis using result by blast
qed

lemma lp_return_shape_entry_projection:
  fixes flt :: "'g afs" and data :: "'f \<Rightarrow> 'g"
    and eta :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  assumes filter: "lp_return_shape_filter_check flt data G"
    and known: "lp_return_shape_known G seeds eta"
    and shape: "s\<noteq>LPReturnAny"
    and checked: "lp_return_shape_check fuel G seeds s t"
  shows "\<exists>u::('g,'v) term. lp_iproject flt (map_lp_iterm data id (lp_ieval t eta)) u"
  by (rule lp_return_shape_filter_projection[OF filter lp_return_shape_check_sound[OF checked known] shape])

end
