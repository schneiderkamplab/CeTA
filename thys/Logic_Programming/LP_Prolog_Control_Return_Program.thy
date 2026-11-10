theory LP_Prolog_Control_Return_Program
 imports LP_Prolog_Control_Return_Paths LP_Prolog_Open_Return_Model
begin

text \<open>Completed logical paths repeat equality premises after helper calls.
This preserves their truth without changing the source execution order. The
open model imposes precise return properties only on covered predicates.\<close>

lemma lpp_control_completed_model:
  assumes "list_all (lpc_model_goal M) (map (lp_cut_map ev) gs)"
  shows "list_all (lpc_model_goal M)
    (map (lp_cut_map ev) (lpp_control_completed_path gs))"
  using assms by (auto simp: lpp_control_completed_path_def list_all_iff)

lemma lpp_control_model_bind_equiv:
  "lpc_model_goal M (lp_cut_bind m ev g) = lpc_model_goal M (lp_cut_map ev g)"
  by (cases g) simp_all

fun lpp_control_flat_goal where
  "lpp_control_flat_goal F (LPCAtom (Fun (LPCUser f) ts)) =
    (f\<in>F \<and> f\<noteq>''2:;'' \<and> f\<noteq>''3:subtract'')"
| "lpp_control_flat_goal F _ = False"

lemma lpp_control_flat_goal_iff:
  "lpp_control_flat_goal F g = (\<exists>f ts. g=LPCAtom (Fun (LPCUser f) ts) \<and>
    f\<in>F \<and> f\<noteq>''2:;'' \<and> f\<noteq>''3:subtract'')"
proof (cases g)
  case (LPCAtom t)
  show ?thesis
  proof (cases t)
    case (Var x) then show ?thesis by (simp add: LPCAtom)
  next
    case (Fun h ts) then show ?thesis by (cases h) (auto simp: LPCAtom)
  qed
qed simp_all

lemma lpp_control_flat_control:
  "lpp_control_flat_goal F g \<Longrightarrow> lpc_return_control_goal F g"
  by (auto simp: lpp_control_flat_goal_iff lpc_return_control_goal_iff lpc_control_goal_iff)

lemma lpp_control_flat_model:
  assumes flat: "lpp_control_flat_goal F g"
    and model: "lpc_model_goal (lpp_control_return_model (lpp_open_return_model F M))
      (lp_cut_map (\<lambda>t. lp_ieval t eta) g)"
  shows "lpc_model_goal M (lp_cut_map (\<lambda>t. lp_ieval t eta) g)"
  using flat model by (auto simp: lpp_control_flat_goal_iff lpp_control_return_ordinary)

lemma lpp_control_flat_body:
  assumes flat: "list_all (lpp_control_flat_goal F) gs"
    and model: "list_all (lpc_model_goal (lpp_control_return_model (lpp_open_return_model F M)))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  shows "list_all (lpc_model_goal M) (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) gs)"
  using flat model lpp_control_flat_model[where F=F and M=M and eta=eta]
  by (auto simp: list_all_iff lpp_control_model_bind_equiv)

end
