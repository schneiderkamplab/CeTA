theory LP_Prolog_Observed_Endpoint_Rewrite
 imports LP_Prolog_Stable_Field_Projection
begin

definition lpp_rewrite_observed_atom where
  "lpp_rewrite_observed_atom s t a = (fst a,map (lp_equation_replace s t) (snd a))"

lemma lpp_rewrite_observed_atom_eval:
  assumes "lp_ieval s eta=lp_ieval t eta"
  shows "lpp_success_atom_eval (lpp_rewrite_observed_atom s t a) eta=lpp_success_atom_eval a eta"
  using assms by (auto simp: lpp_rewrite_observed_atom_def lpp_success_atom_eval_def
    map_map lp_equation_replace_eval intro!: map_cong)

fun lpp_rewrite_endpoint_step where
  "lpp_rewrite_endpoint_step (s,t) ((h,ps,b,gs),os) =
    (if LPPOEquation s t\<in>set os then
      ((lpp_rewrite_observed_atom s t h,ps,lpp_rewrite_observed_atom s t b,gs),os)
     else ((h,ps,b,gs),os))"

lemma lpp_rewrite_endpoint_step_sound:
  "lpp_stable_observed_calls operation {candidate_row} P \<subseteq>
    lpp_stable_observed_calls operation {lpp_rewrite_endpoint_step equation candidate_row} P"
proof -
  obtain s t where equation_pair: "equation=(s,t)" by (cases equation) auto
  obtain h ps b gs os where row_data: "candidate_row=((h,ps,b,gs),os)" by (cases candidate_row) auto
  show ?thesis
  proof (cases "LPPOEquation s t\<in>set os")
    case False then show ?thesis by (simp add: equation_pair row_data)
  next
    case True
    show ?thesis
    proof
      fix edge
      assume member: "edge\<in>lpp_stable_observed_calls operation {candidate_row} P"
      obtain a sigma eta where edge: "edge=(a,lpp_success_atom_eval b eta)"
        and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
        and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
        and observed: "list_all (lpp_stable_observation_holds operation eta) os"
        and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
          (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
        using member unfolding row_data lpp_stable_observed_calls_def by blast
      have equal: "lp_ieval s eta=lp_ieval t eta"
        using observed True by (auto simp: list_all_iff)
      have head_eval: "lpp_success_atom_eval (lpp_rewrite_observed_atom s t h) eta=lpp_success_atom_eval h eta"
        by (rule lpp_rewrite_observed_atom_eval[OF equal])
      have call_eval: "lpp_success_atom_eval (lpp_rewrite_observed_atom s t b) eta=lpp_success_atom_eval b eta"
        by (rule lpp_rewrite_observed_atom_eval[OF equal])
      show "edge\<in>lpp_stable_observed_calls operation {lpp_rewrite_endpoint_step equation candidate_row} P"
        unfolding equation_pair row_data lpp_rewrite_endpoint_step.simps if_P[OF True]
          edge lpp_stable_observed_calls_def
        apply (rule CollectI)
        apply (rule exI[of _ a], rule exI[of _ "lpp_rewrite_observed_atom s t h"],
          rule exI[of _ ps], rule exI[of _ "lpp_rewrite_observed_atom s t b"],
          rule exI[of _ gs], rule exI[of _ os], rule exI[of _ sigma], rule exI[of _ eta])
        using matching guards observed helpers head_eval call_eval by simp
    qed
  qed
qed

fun lpp_rewrite_endpoint_steps where
  "lpp_rewrite_endpoint_steps [] candidate_row = candidate_row"
| "lpp_rewrite_endpoint_steps (equation_pair#eqs) candidate_row =
    lpp_rewrite_endpoint_steps eqs (lpp_rewrite_endpoint_step equation_pair candidate_row)"

lemma lpp_rewrite_endpoint_steps_sound:
  "lpp_stable_observed_calls operation {candidate_row} P \<subseteq>
    lpp_stable_observed_calls operation {lpp_rewrite_endpoint_steps eqs candidate_row} P"
proof (induct eqs arbitrary: candidate_row)
  case Nil then show ?case by simp
next
  case (Cons equation_pair eqs)
  show ?case using subset_trans[OF lpp_rewrite_endpoint_step_sound Cons] by simp
qed

definition lpp_rewrite_endpoints where
  "lpp_rewrite_endpoints fuel candidate_row =
    lpp_rewrite_endpoint_steps (take fuel (lpp_observed_equations (snd candidate_row))) candidate_row"

lemma lpp_rewrite_endpoints_sound:
  "lpp_stable_observed_calls operation (set observed_rows) P \<subseteq>
    lpp_stable_observed_calls operation (set (map (lpp_rewrite_endpoints fuel) observed_rows)) P"
proof (induct observed_rows)
  case Nil then show ?case by (simp add: lpp_stable_observed_calls_def)
next
  case (Cons a observed_rows)
  have head: "lpp_stable_observed_calls operation {a} P \<subseteq>
      lpp_stable_observed_calls operation {lpp_rewrite_endpoints fuel a} P"
    unfolding lpp_rewrite_endpoints_def by (rule lpp_rewrite_endpoint_steps_sound)
  show ?case using head Cons by (simp only: list.map lpp_stable_observed_calls_Cons; blast)
qed

ML \<open>
val checked = [@{thm lpp_rewrite_endpoints_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted endpoint equation rewrite dependency" else ();
\<close>
end
