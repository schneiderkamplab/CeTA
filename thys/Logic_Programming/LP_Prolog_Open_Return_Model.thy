theory LP_Prolog_Open_Return_Model
 imports LP_Prolog_Inline_Probe_Return
begin

fun lpp_open_return_model where
  "lpp_open_return_model F M (LPIFun (LPCUser f) ts) =
    (if f\<in>F then M (LPIFun (LPCUser f) ts) else True)"
| "lpp_open_return_model F M _ = False"

lemma lpp_open_return_model_subst:
  assumes stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and known: "lpp_open_return_model F M t"
  shows "lpp_open_return_model F M (lp_isubst t sigma)"
proof (cases t)
  case (LPIVar x)
  then show ?thesis using known by simp
next
  case (LPIFun f ts)
  then show ?thesis using known stable[of t sigma]
    by (cases f) auto
qed

lemma lpp_open_return_body:
  assumes control: "list_all (lpc_return_control_goal F) gs"
    and known: "list_all (lpc_model_goal (lpp_open_return_model F M))
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) gs)"
  shows "list_all (lpc_model_goal M) (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) gs)"
  using control known
  by (induct gs) (auto simp: lpc_return_control_goal_iff lpc_control_goal_iff)

text \<open>Outside the selected predicate set this model asserts no return
property. It does not remove source calls or prove that any call terminates.\<close>

ML \<open>
val checked = [@{thm lpp_open_return_model_subst},@{thm lpp_open_return_body}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted open return model" else ();
\<close>
end
