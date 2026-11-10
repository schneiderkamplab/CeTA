theory LP_Return_Shape_Projection
 imports LP_Return_Shapes LP_Dependency_Triple_Observed_Roles LP_Dependency_Triple_Projected_Query
begin

text \<open>The filter observes only inductively finite shape edges. An Any
field may be open or cyclic, so retaining it is rejected. This check concerns
all productions, not a chosen successful example of the grammar.\<close>

definition lp_return_shape_filter_check where
  "lp_return_shape_filter_check flt data G = list_all (\<lambda>productions.
    list_all (\<lambda>(f,shapes). case Argument_Filter.afs flt (data f,length shapes) of
      AFList indices \<Rightarrow> list_all (\<lambda>i. i<length shapes \<and> shapes!i\<noteq>LPReturnAny) indices
    | Collapse i \<Rightarrow> i<length shapes \<and> shapes!i\<noteq>LPReturnAny) productions) G"

lemma lp_return_shape_filter_projection:
  fixes flt :: "'g afs" and data :: "'f \<Rightarrow> 'g"
    and t :: "('f,'v) lp_iterm"
  assumes checked: "lp_return_shape_filter_check flt data G"
    and shape: "lp_return_shape_holds G s t"
    and observed: "s\<noteq>LPReturnAny"
  shows "\<exists>u::('g,'v) term. lp_iproject flt (map_lp_iterm data id t) u"
  using shape observed
proof (induct rule: lp_return_shape_holds.induct)
  case (any t)
  then show ?case by simp
next
  case (ground t)
  have finite: "lp_seg_ground (map_lp_iterm data id t)"
    by (rule lp_seg_ground_map_symbols[OF ground.hyps])
  have projected: "\<exists>u::('g,'v) term. lp_iproject flt
      (map_lp_iterm id id (map_lp_iterm data id t)) u"
    by (rule lp_seg_ground_mapped_projection[OF finite])
  show ?case using projected by (simp only: lp_iterm.map_id)
next
  case (node i f shapes ts)
  have production: "case Argument_Filter.afs flt (data f,length shapes) of
      AFList indices \<Rightarrow> list_all (\<lambda>j. j<length shapes \<and> shapes!j\<noteq>LPReturnAny) indices
    | Collapse j \<Rightarrow> j<length shapes \<and> shapes!j\<noteq>LPReturnAny"
    using checked node.hyps(1,2)
    by (auto simp: lp_return_shape_filter_check_def list_all_iff dest: nth_mem)
  show ?case
  proof (cases "Argument_Filter.afs flt (data f,length shapes)")
    case (AFList indices)
    have each: "\<exists>u::('g,'v) term. lp_iproject flt (map_lp_iterm data id (ts!j)) u"
      if "j\<in>set indices" for j
      using production AFList that node.hyps(3) node.hyps
      by (auto simp: list_all_iff id_def)
    let ?pick = "\<lambda>j. SOME u::('g,'v) term. lp_iproject flt (map_lp_iterm data id (ts!j)) u"
    have witness: "lp_iproject flt (map_lp_iterm data id (ts!j)) (?pick j)"
      if "j\<in>set indices" for j
      by (rule someI_ex) (use each[OF that] in blast)
    have result: "lp_iproject flt (LPIFun (data f) (map (map_lp_iterm data id) ts))
        (Fun (data f) (map ?pick indices))"
      by (rule lp_iproject.list[where indices=indices])
        (use AFList production node.hyps(3) witness in
          \<open>auto simp: list_all2_map2 list_all2_same list_all_iff\<close>)
    show ?thesis using result by (auto simp: id_def)
  next
    case (Collapse j)
    have bound: "j<length ts" and selected: "shapes!j\<noteq>LPReturnAny"
      using production Collapse node.hyps(3) by auto
    obtain u::"('g,'v) term" where child: "lp_iproject flt (map_lp_iterm data id (ts!j)) u"
      using node.hyps bound selected by (auto simp: id_def)
    have "lp_iproject flt (LPIFun (data f) (map (map_lp_iterm data id) ts)) u"
      by (rule lp_iproject.collapse[where i=j]) (use Collapse node.hyps(3) bound child in auto)
    then show ?thesis by (auto simp: id_def)
  qed
qed

ML \<open>
val checked = [@{thm lp_return_shape_filter_projection}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted return shape projection" else ();
\<close>
end
