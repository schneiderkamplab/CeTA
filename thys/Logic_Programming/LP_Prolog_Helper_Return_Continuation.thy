theory LP_Prolog_Helper_Return_Continuation
  imports LP_Prolog_Guarded_Helper_Return
begin

text \<open>Composition of an actual helper return with a caller guard. The
success case keeps every helper alternative. Failure may resume the caller
only after the helper alternatives are exhausted; the unique remaining-clause
case below exposes this requirement in the returned stack itself.\<close>

lemma lpp_helper_return_guard_success:
  assumes returned: "(start,LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
      (LPCAtom (LPIFun (LPCUser f) [a,b])#rest))#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    and descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_integer_evaluation (lp_isubst a sigma) n"
    and right: "lpp_integer_evaluation (lp_isubst b sigma) m"
    and holds: "lpp_integer_compare c (if reversed then m else n) (if reversed then n else m)"
  shows "(start,LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) rest)#saved)
    \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  note guard = lpp_integer_recurrence_comparison_success[OF descriptor left right holds,
    where gs="map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) rest" and es=saved and P=P]
  show ?thesis using returned guard by (auto intro: trancl_trans r_into_trancl)
qed

lemma lpp_helper_return_guard_failure:
  assumes returned: "\<exists>mark. (start,LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
      (LPCAtom (LPIFun (LPCUser f) [a,b])#rest))#LPCBarrier mark#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    and descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_integer_evaluation (lp_isubst a sigma) n"
    and right: "lpp_integer_evaluation (lp_isubst b sigma) m"
    and fails: "\<not>lpp_integer_compare c (if reversed then m else n) (if reversed then n else m)"
  shows "(start,saved)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  obtain mark where path: "(start,LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
      (LPCAtom (LPIFun (LPCUser f) [a,b])#rest))#LPCBarrier mark#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using returned by blast
  note guard = lpp_integer_recurrence_comparison_failure[OF descriptor left right fails,
    where gs="map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) rest" and es="LPCBarrier mark#saved" and P=P]
  have failed: "(start,LPCBarrier mark#saved)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using path guard by (auto intro: trancl_trans r_into_trancl)
  have admin: "(LPCBarrier mark#saved,saved)\<in>lp_cut_mgu_source P"
    by (rule lp_cut_mgu_source.admin) simp
  have restored: "(LPCBarrier mark#saved,saved)\<in>lpp_builtin_source P lpp_integer_source_builtin"
    using admin by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  show ?thesis using failed restored by (meson trancl_trans r_into_trancl)
qed

ML \<open>
val checked = [@{thm lpp_helper_return_guard_success}, @{thm lpp_helper_return_guard_failure}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper continuation dependency" else ();
\<close>
end
