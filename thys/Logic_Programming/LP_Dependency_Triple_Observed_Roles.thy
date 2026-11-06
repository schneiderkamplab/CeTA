theory LP_Dependency_Triple_Observed_Roles
 imports LP_Dependency_Triple_Observed_Query LP_Dependency_Triple_Roles LP_Cut_Return_Residual_Query
begin

theorem check_lp_triple_pidp_observed_roles_sound:
  fixes fallback :: "(string,nat list) lab"
    and ts :: "('f,string) lp_iterm list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and child: "check_lp_triple_pidp I J (lp_roles_triples p d D) (lp_roles_program p d P)
      outs fallback dnames pnames marks filters (p q) n positions labs proofs"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> lp_seg_ground (ts!i)"
  shows "SN_on (lp_triple_calls (set D) P) {(q,ts)}"
proof -
  have mapped_ground: "lp_seg_ground ((map (map_lp_iterm d id) ts)!i)"
    if "i\<in>set positions" "i<n" for i
    using lp_seg_ground_map_symbols[OF gr[OF that], of d] that len by simp
  have child_sn: "SN_on (lp_triple_calls (set (lp_roles_triples p d D)) (lp_roles_program p d P))
      {(p q,map (map_lp_iterm d id) ts)}"
    by (rule check_lp_triple_pidp_observed_sound[OF I J child _ mapped_ground]) (simp add: len)
  show ?thesis
    by (rule lp_roles_triple_termination_reflect[where p=p and d=d])
      (use child_sn in \<open>simp add: lp_roles_iatom_def\<close>)
qed

ML \<open>
val checked = [@{thm check_lp_triple_pidp_observed_roles_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted observed triple roles" else ();
\<close>
end
