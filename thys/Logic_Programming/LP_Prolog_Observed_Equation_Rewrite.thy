theory LP_Prolog_Observed_Equation_Rewrite
  imports LP_Prolog_Stable_Observed_Calls LP_Equation_Congruence
begin

text \<open>Rewrite observations only from an equation established in that same
observed call. Endpoints and successful-helper obligations are unchanged.
This supplies no integer typing or arithmetic bound.\<close>

fun lpp_rewrite_success_guard where
  "lpp_rewrite_success_guard s t (LPPSInteger a) = LPPSInteger (lp_equation_replace s t a)"
| "lpp_rewrite_success_guard s t (LPPSEvaluates e a) =
    LPPSEvaluates (lp_equation_replace s t e) (lp_equation_replace s t a)"
| "lpp_rewrite_success_guard s t (LPPSOpaque a) = LPPSOpaque (lp_equation_replace s t a)"

fun lpp_rewrite_observation where
  "lpp_rewrite_observation s t (LPPOGround a) = LPPOGround (lp_equation_replace s t a)"
| "lpp_rewrite_observation s t (LPPOEquation a b) =
    LPPOEquation (lp_equation_replace s t a) (lp_equation_replace s t b)"
| "lpp_rewrite_observation s t (LPPOShape G shape a) = LPPOShape G shape (lp_equation_replace s t a)"
| "lpp_rewrite_observation s t (LPPOInteger a) = LPPOInteger (lp_equation_replace s t a)"
| "lpp_rewrite_observation s t (LPPOEvaluation e a) =
    LPPOEvaluation (lp_equation_replace s t e) (lp_equation_replace s t a)"
| "lpp_rewrite_observation s t (LPPOComparison c a b) =
    LPPOComparison c (lp_equation_replace s t a) (lp_equation_replace s t b)"

lemma lpp_rewrite_success_guard_holds:
  assumes "lp_ieval s eta=lp_ieval t eta"
  shows "lpp_success_guard_holds E eta (lpp_rewrite_success_guard s t g) =
    lpp_success_guard_holds E eta g"
  by (cases g) (simp_all add: lp_equation_replace_eval[OF assms])

lemma lpp_rewrite_observation_holds:
  assumes "lp_ieval s eta=lp_ieval t eta"
  shows "lpp_stable_observation_holds operation eta (lpp_rewrite_observation s t observation) =
    lpp_stable_observation_holds operation eta observation"
  by (cases observation) (simp_all add: lp_equation_replace_eval[OF assms])

lemma lpp_rewrite_observed_call:
  assumes equation: "LPPOEquation s t\<in>set observations"
  shows "lpp_stable_observed_calls operation {((h,ps,b,gs),observations)} P \<subseteq>
    lpp_stable_observed_calls operation
      {((h,ps,b,map (lpp_rewrite_success_guard s t) gs),map (lpp_rewrite_observation s t) observations)} P"
proof
  fix edge
  assume member: "edge\<in>lpp_stable_observed_calls operation {((h,ps,b,gs),observations)} P"
  obtain a sigma eta where edge: "edge=(a,lpp_success_atom_eval b eta)"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observed: "list_all (lpp_stable_observation_holds operation eta) observations"
    and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    using member by (simp only: lpp_stable_observed_calls_def; blast)
  have equal: "lp_ieval s eta=lp_ieval t eta"
    using observed equation by (auto simp: list_all_iff)
  have guards': "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
      (map (lpp_rewrite_success_guard s t) gs)"
    using guards by (simp add: list_all_iff lpp_rewrite_success_guard_holds[OF equal])
  have observed': "list_all (lpp_stable_observation_holds operation eta)
      (map (lpp_rewrite_observation s t) observations)"
    using observed by (simp add: list_all_iff lpp_rewrite_observation_holds[OF equal])
  show "edge\<in>lpp_stable_observed_calls operation
      {((h,ps,b,map (lpp_rewrite_success_guard s t) gs),map (lpp_rewrite_observation s t) observations)} P"
    unfolding edge lpp_stable_observed_calls_def
    using matching guards' observed' helpers by blast
qed

text \<open>Enrichment retains original typing and shape observations. It is
therefore suitable before residual projection, which may need both a symbolic
endpoint type and the enriched_rows arithmetic expression.\<close>

lemma lpp_enrich_observed_call:
  assumes equation: "LPPOEquation s t\<in>set observations"
  shows "lpp_stable_observed_calls operation {((h,ps,b,gs),observations)} P \<subseteq>
    lpp_stable_observed_calls operation
      {((h,ps,b,gs @ map (lpp_rewrite_success_guard s t) gs),observations @ map (lpp_rewrite_observation s t) observations)} P"
proof
  fix edge
  assume member: "edge\<in>lpp_stable_observed_calls operation {((h,ps,b,gs),observations)} P"
  obtain a sigma eta where edge: "edge=(a,lpp_success_atom_eval b eta)"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observed: "list_all (lpp_stable_observation_holds operation eta) observations"
    and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    using member by (simp only: lpp_stable_observed_calls_def; blast)
  have equal: "lp_ieval s eta=lp_ieval t eta"
    using observed equation by (auto simp: list_all_iff)
  have guards': "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
      (map (lpp_rewrite_success_guard s t) gs)"
    using guards by (simp add: list_all_iff lpp_rewrite_success_guard_holds[OF equal])
  have observed': "list_all (lpp_stable_observation_holds operation eta)
      (map (lpp_rewrite_observation s t) observations)"
    using observed by (simp add: list_all_iff lpp_rewrite_observation_holds[OF equal])
  have combined_guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
      (gs @ map (lpp_rewrite_success_guard s t) gs)"
    using guards guards' by simp
  have combined_observed: "list_all (lpp_stable_observation_holds operation eta)
      (observations @ map (lpp_rewrite_observation s t) observations)"
    using observed observed' by simp
  show "edge\<in>lpp_stable_observed_calls operation
      {((h,ps,b,gs @ map (lpp_rewrite_success_guard s t) gs),observations @ map (lpp_rewrite_observation s t) observations)} P"
    unfolding edge lpp_stable_observed_calls_def
    using matching combined_guards combined_observed helpers by blast
qed


fun lpp_enrich_observed_step where
  "lpp_enrich_observed_step (s,t) ((h,ps,b,gs),os) =
    (if LPPOEquation s t\<in>set os then
      ((h,ps,b,remdups (gs @ map (lpp_rewrite_success_guard s t) gs)),
       remdups (os @ map (lpp_rewrite_observation s t) os))
     else ((h,ps,b,gs),os))"

lemma lpp_observed_calls_remdups:
  "lpp_stable_observed_calls operation {((h,ps,b,remdups gs),remdups os)} P =
    lpp_stable_observed_calls operation {((h,ps,b,gs),os)} P"
  by (auto simp: lpp_stable_observed_calls_def list_all_iff)

lemma lpp_enrich_observed_step_sound:
  "lpp_stable_observed_calls operation {candidate_row} P \<subseteq>
    lpp_stable_observed_calls operation {lpp_enrich_observed_step equation candidate_row} P"
proof -
  obtain s t where equation: "equation=(s,t)" by (cases equation) auto
  obtain h ps b gs os where candidate_row: "candidate_row=((h,ps,b,gs),os)" by (cases candidate_row) auto
  show ?thesis
  proof (cases "LPPOEquation s t\<in>set os")
    case True
    note inclusion = lpp_enrich_observed_call[OF True, of operation h ps b gs P]
    show ?thesis using inclusion
      by (simp only: equation candidate_row lpp_enrich_observed_step.simps True if_True lpp_observed_calls_remdups)
  next
    case False
    then show ?thesis by (simp add: equation candidate_row)
  qed
qed

fun lpp_enrich_observed_steps where
  "lpp_enrich_observed_steps [] candidate_row = candidate_row"
| "lpp_enrich_observed_steps (equation#equations) candidate_row =
    lpp_enrich_observed_steps equations (lpp_enrich_observed_step equation candidate_row)"

lemma lpp_enrich_observed_steps_sound:
  "lpp_stable_observed_calls operation {candidate_row} P \<subseteq>
    lpp_stable_observed_calls operation {lpp_enrich_observed_steps equations candidate_row} P"
proof (induct equations arbitrary: candidate_row)
  case Nil
  then show ?case by simp
next
  case (Cons equation equations)
  show ?case using subset_trans[OF lpp_enrich_observed_step_sound Cons]
    by simp
qed

fun lpp_observed_equations where
  "lpp_observed_equations [] = []"
| "lpp_observed_equations (LPPOEquation (Var x) t # os) = (Var x,t)#lpp_observed_equations os"
| "lpp_observed_equations (_ # os) = lpp_observed_equations os"

definition lpp_normalize_observed_row where
  "lpp_normalize_observed_row fuel candidate_row =
    lpp_enrich_observed_steps (take fuel (lpp_observed_equations (snd candidate_row))) candidate_row"

lemma lpp_stable_observed_calls_mono:
  assumes "D\<subseteq>E"
  shows "lpp_stable_observed_calls operation D P \<subseteq> lpp_stable_observed_calls operation E P"
  using assms unfolding lpp_stable_observed_calls_def by blast

lemma lpp_normalize_observed_calls:
  "lpp_stable_observed_calls operation (set observed_rows) P \<subseteq>
    lpp_stable_observed_calls operation (set (map (lpp_normalize_observed_row fuel) observed_rows)) P"
proof
  fix edge
  assume member: "edge\<in>lpp_stable_observed_calls operation (set observed_rows) P"
  then obtain candidate_row where candidate_row: "candidate_row\<in>set observed_rows"
    and edge: "edge\<in>lpp_stable_observed_calls operation {candidate_row} P"
    by (simp only: lpp_stable_observed_calls_def; blast)
  have enriched_rows: "edge\<in>lpp_stable_observed_calls operation {lpp_normalize_observed_row fuel candidate_row} P"
    using lpp_enrich_observed_steps_sound edge
    unfolding lpp_normalize_observed_row_def by blast
  have normalized_member: "lpp_normalize_observed_row fuel candidate_row\<in>set (map (lpp_normalize_observed_row fuel) observed_rows)"
    using candidate_row by simp
  have included_rows: "{lpp_normalize_observed_row fuel candidate_row} \<subseteq> set (map (lpp_normalize_observed_row fuel) observed_rows)"
    using normalized_member by simp
  show "edge\<in>lpp_stable_observed_calls operation (set (map (lpp_normalize_observed_row fuel) observed_rows)) P"
    using enriched_rows lpp_stable_observed_calls_mono[OF included_rows, of operation P] by blast
qed

fun lpp_observed_row_equivalent where
  "lpp_observed_row_equivalent ((h,ps,b,gs),os) ((h',ps',b',gs'),os') =
    (h = h' \<and> ps = ps' \<and> b = b' \<and> list_all (\<lambda>g. g\<in>set gs') gs \<and> list_all (\<lambda>g. g\<in>set gs) gs' \<and>
      list_all (\<lambda>obs. obs\<in>set os') os \<and> list_all (\<lambda>obs. obs\<in>set os) os')"

lemma lpp_observed_row_equivalent_sound:
  assumes "lpp_observed_row_equivalent a b"
  shows "lpp_stable_observed_calls operation {a} P = lpp_stable_observed_calls operation {b} P"
  using assms
  by (cases a; cases b; auto simp: lpp_stable_observed_calls_def list_all_iff; blast)

lemma lpp_stable_observed_calls_Cons:
  "lpp_stable_observed_calls operation (set (a#as)) P =
    lpp_stable_observed_calls operation {a} P \<union> lpp_stable_observed_calls operation (set as) P"
  by (auto simp: lpp_stable_observed_calls_def; blast)

definition lpp_check_observed_normalization where
  "lpp_check_observed_normalization fuel originals enriched_rows =
    list_all2 (\<lambda>a b. lpp_observed_row_equivalent (lpp_normalize_observed_row fuel a) b) originals enriched_rows"

lemma lpp_check_observed_normalization_sound:
  assumes "lpp_check_observed_normalization fuel originals enriched_rows"
  shows "(lpp_stable_observed_calls operation (set originals) P :: string lpp_success_iatom rel) \<subseteq>
    lpp_stable_observed_calls operation (set enriched_rows) P"
  using assms unfolding lpp_check_observed_normalization_def
proof (induct originals arbitrary: enriched_rows)
  case Nil
  then show ?case by (simp add: lpp_stable_observed_calls_def)
next
  case (Cons a originals)
  then obtain b bs where enriched_rows: "enriched_rows = b#bs"
    and equivalent: "lpp_observed_row_equivalent (lpp_normalize_observed_row fuel a) b"
    and tail: "list_all2 (\<lambda>a b. lpp_observed_row_equivalent (lpp_normalize_observed_row fuel a) b) originals bs"
    by (cases enriched_rows) auto
  have normalized_head: "(lpp_stable_observed_calls operation {a} P :: string lpp_success_iatom rel) \<subseteq>
    lpp_stable_observed_calls operation {lpp_normalize_observed_row fuel a} P"
    unfolding lpp_normalize_observed_row_def by (rule lpp_enrich_observed_steps_sound)
  have same: "(lpp_stable_observed_calls operation {lpp_normalize_observed_row fuel a} P :: string lpp_success_iatom rel) =
    lpp_stable_observed_calls operation {b} P"
    by (rule lpp_observed_row_equivalent_sound[OF equivalent])
  have head: "(lpp_stable_observed_calls operation {a} P :: string lpp_success_iatom rel) \<subseteq>
    lpp_stable_observed_calls operation {b} P"
    using normalized_head same by simp
  show ?case
    unfolding enriched_rows lpp_stable_observed_calls_Cons
    by (rule Un_mono[OF head Cons.hyps[OF tail]])
qed

ML \<open>
val checked = [@{thm lpp_rewrite_observed_call}, @{thm lpp_enrich_observed_call}, @{thm lpp_normalize_observed_calls}, @{thm lpp_check_observed_normalization_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted observed equation rewrite dependency" else ();
\<close>
end
