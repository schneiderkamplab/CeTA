theory LP_Cut_SEG_Projected_Emit
  imports LP_Cut_SEG_Projected_Measure LP_Cut_SEG_Roles
begin

hide_const (open) CPF_Proof_Parser.rstep

text \<open>Projected extraction may have extra variables before filtering.
The variable condition is checked on the filtered rules, and the child
obligation is full rewriting termination, not an implicit innermost claim.\<close>

definition lpc_seg_check_projected_pair where
  "lpc_seg_check_projected_pair filtering nl nr is_cont c d R l r =
    (lpc_seg_role_shape nl is_cont l \<and> lpc_seg_role_shape nr is_cont r \<and>
      (let left=lpc_seg_role_term nl is_cont c d l;
           right=lpc_seg_role_term nr is_cont c d r in
       (left,right)\<in>R \<and>
       vars_term (af_term filtering right) \<subseteq> vars_term (af_term filtering left)))"

theorem lpc_seg_checked_projected_pair:
  fixes pi :: "'g afs" and measure :: "('g,'v) term"
  assumes checked: "lpc_seg_check_projected_pair pi nl nr is_cont c d R l r"
    and observed: "lp_iproject pi (lpc_seg_role_value nl is_cont c d (lp_ieval l eta)) measure"
  obtains result where
    "lp_iproject pi (lpc_seg_role_value nr is_cont c d (lp_ieval r eta)) result"
    "(measure,result)\<in>rstep (af_rule pi ` R)"
proof -
  have ls: "lpc_seg_role_shape nl is_cont l" and rs: "lpc_seg_role_shape nr is_cont r"
    and rule: "(lpc_seg_role_term nl is_cont c d l,lpc_seg_role_term nr is_cont c d r)\<in>R"
    and vars: "vars_term (af_term pi (lpc_seg_role_term nr is_cont c d r)) \<subseteq>
      vars_term (af_term pi (lpc_seg_role_term nl is_cont c d l))"
    using checked by (auto simp: lpc_seg_check_projected_pair_def Let_def)
  have pr: "lp_iproject pi (lp_ieval (lpc_seg_role_term nl is_cont c d l)
      (\<lambda>x. map_lp_iterm d id (eta x))) measure"
    using observed by (simp only: lpc_seg_role_eval[OF ls])
  obtain result where target: "lp_iproject pi (lp_ieval (lpc_seg_role_term nr is_cont c d r)
      (\<lambda>x. map_lp_iterm d id (eta x))) result"
    and step: "(measure,result)\<in>rstep (af_rule pi ` R)"
    using lp_infinite_rule_projection[OF pr vars rule] by blast
  show thesis by (rule that[OF _ step])
    (use target in \<open>simp only: lpc_seg_role_eval[OF rs]\<close>)
qed

end
