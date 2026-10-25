theory LP_Cut_Return_Projection
  imports LP_Cut_Return_Resolution
begin

hide_const (open) CPF_Proof_Parser.afs

text \<open>A finite filtered observation is stable under resolution even when
the unfiltered answer is neither ground nor finite. This does not identify
the old and new runtime values: only their checked projections agree. In
particular, saved alternatives must retain their original environments.\<close>

lemma lpc_return_projection_after_substitution:
  fixes pi :: "'f afs"
    and measure :: "('f,'v) term"
  assumes observed: "lp_iproject pi (lp_ieval t eta) measure"
  shows "lp_iproject pi (lp_isubst (lp_ieval t eta) sigma) measure"
  by (rule lp_iproject_subst[OF observed])

lemma lpc_checked_return_projection:
  fixes pi :: "'f afs"
    and measure :: "('f,'v) term"
  assumes checked: "lpc_check_return_values fuel k G eqs active saved result"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and equations: "lp_equations eqs (lp_cut_resolution_env k l eta sigma rho)"
    and index: "i < length active"
    and observed: "lp_iproject pi (lp_ieval (active!i) eta) measure"
  shows "i < length result"
    and "lp_iproject pi
      (lp_ieval (result!i) (lp_cut_resolution_env k l eta sigma rho)) measure"
proof -
  have evaluated: "map (\<lambda>t. lp_ieval t (lp_cut_resolution_env k l eta sigma rho)) result =
      map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) active"
    by (rule lpc_checked_return_values(1)[OF checked bounds ground equations])
  have lengths: "length result = length active"
    using arg_cong[OF evaluated, of length] by simp
  show valid: "i < length result" using index lengths by simp
  have eq: "lp_ieval (result!i) (lp_cut_resolution_env k l eta sigma rho) =
      lp_isubst (lp_ieval (active!i) eta) sigma"
    using arg_cong[OF evaluated, of "\<lambda>xs. xs!i"] index valid by simp
  show "lp_iproject pi
      (lp_ieval (result!i) (lp_cut_resolution_env k l eta sigma rho)) measure"
    unfolding eq by (rule lp_iproject_subst[OF observed])
qed

lemma lpc_projection_environment:
  fixes pi :: "'f afs" and measure :: "('f,'v) term"
  assumes observed: "lp_iproject pi (lp_ieval t eta) measure"
    and preserved: "\<And>x (u::('f,'v) term). x\<in>vars_term (af_term pi t) \<Longrightarrow>
      lp_iproject pi (eta x) u \<Longrightarrow> lp_iproject pi (nu x) u"
  shows "lp_iproject pi (lp_ieval t nu) measure"
proof -
  have available: "lp_iproject pi (nu x) (lp_projection pi (eta x) :: ('f,'v) term)"
    if member: "x\<in>vars_term (af_term pi t)" for x
  proof -
    obtain u :: "('f,'v) term" where pr: "lp_iproject pi (eta x) u"
      using lp_iproject_ieval_variables[OF observed member] by blast
    have eq: "lp_projection pi (eta x)=u" by (rule lp_projection_eq[OF pr])
    show ?thesis unfolding eq by (rule preserved[OF member pr])
  qed
  have eq: "measure = af_term pi t \<cdot> (\<lambda>x. lp_projection pi (eta x))"
    by (rule lp_iproject_ieval_inverse[OF observed])
  show ?thesis unfolding eq by (rule lp_iproject_ieval_forward[OF available])
qed

definition lpc_observation_refresh where
  "lpc_observation_refresh k G A x =
    (if x\<in>A then lp_cut_refresh k G x else Var x)"

lemma lpc_filtered_variables:
  fixes pi :: "'f afs"
  shows "vars_term (af_term pi t) \<subseteq> vars_term t"
proof (induct t)
  case (Var x) then show ?case by simp
next
  case (Fun f ts)
  have child: "vars_term (af_term pi (ts!i)) \<subseteq> vars_term (Fun f ts)"
    if "i<length ts" for i
    using Fun[OF nth_mem[OF that]] nth_mem[OF that] by auto
  have wf: "wf_af_entry (length ts) (afs pi (f,length ts))"
    by (rule Argument_Filter.afs)
  show ?case
  proof (cases "afs pi (f,length ts)")
    case (Collapse i)
    have bound: "i<length ts" using wf Collapse by simp
    show ?thesis using child[OF bound] by (simp add: Collapse bound)
  next
    case (AFList indices)
    have valid: "i<length ts" if "i\<in>set indices" for i
      using wf AFList that by auto
    have children: "vars_term (map (af_term pi) ts ! i) \<subseteq> vars_term (Fun f ts)"
      if "i\<in>set indices" for i
      using child[OF valid[OF that]] valid[OF that] by simp
    show ?thesis using children by (auto simp: AFList)
  qed
qed

lemma lpc_resolution_projected_observation:
  fixes pi :: "'f afs" and measure :: "('f,'v) term"
  assumes observed: "lp_iproject pi (lp_ieval t eta) measure"
    and short: "\<forall>x\<in>vars_term t. length x<k"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
  shows "lp_iproject pi
    (lp_ieval (t\<cdot>lpc_observation_refresh k G A)
      (lp_cut_resolution_env k l eta sigma rho)) measure"
proof -
  let ?env = "lp_cut_resolution_env k l eta sigma rho"
  let ?nu = "\<lambda>x. lp_ieval (lpc_observation_refresh k G A x) ?env"
  have preserved: "lp_iproject pi (?nu x) u"
    if member: "x\<in>vars_term (af_term pi t)"
      and pr: "lp_iproject pi (eta x) u" for x u
  proof -
    have short_x: "length x<k"
      using short member lpc_filtered_variables[of pi t] by blast
    show ?thesis
    proof (cases "x\<in>A")
      case True
      have eq: "lp_ieval (lp_cut_refresh k G x) ?env = lp_isubst (eta x) sigma"
        using lp_cut_resolution_active[where t="Var x", OF _ bounds ground] short_x by simp
      show ?thesis using lp_iproject_subst[OF pr, of sigma]
        by (simp add: lpc_observation_refresh_def True eq)
    next
      case False
      have kl: "k\<le>l" using bounds by arith
      have eq: "?env x=eta x"
        using lp_cut_resolution_old[where t="Var x", OF _ kl] short_x by simp
      show ?thesis using pr by (simp add: lpc_observation_refresh_def False eq)
    qed
  qed
  have "lp_iproject pi (lp_ieval t ?nu) measure"
    by (rule lpc_projection_environment[OF observed preserved])
  then show ?thesis by (simp add: lp_ieval_finite_subst)
qed

end
