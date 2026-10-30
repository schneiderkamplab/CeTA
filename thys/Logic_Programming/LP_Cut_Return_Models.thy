theory LP_Cut_Return_Models
 imports LP_Cut_Answer_Control LP_Cut_Return_Preserved_Ground
begin

text \<open>Successful-return properties are checked independently of termination.
The model invariant follows each saved frame's own answer environment. It may
be instantiated by conditional integer summaries as well as structural models.
This theory reuses the shared answer transition; it defines no new execution.\<close>

fun lpc_model_safe_goal where
  "lpc_model_safe_goal (LPCMeta _) = False"
| "lpc_model_safe_goal _ = True"

fun lpc_model_goal where
  "lpc_model_goal M (LPCAtom t) = M t"
| "lpc_model_goal M (LPCUnify a b) = (a=b)"
| "lpc_model_goal M LPCFail = False"
| "lpc_model_goal M (LPCMeta _) = False"
| "lpc_model_goal M _ = True"

lemma lpc_model_safe_map[simp]:
  "lpc_model_safe_goal (lp_cut_map f g)=lpc_model_safe_goal g"
  by (cases g) simp_all
lemma lpc_model_safe_bind[simp]:
  "lpc_model_safe_goal (lp_cut_bind m f g)=lpc_model_safe_goal g"
  by (cases g) simp_all
lemma lpc_model_bind_map:
  "lp_cut_map f (lp_cut_bind m h g)=lp_cut_bind m (f o h) g"
  by (cases g) simp_all

definition lpc_model_program where
  "lpc_model_program P M = (\<forall>c<length P.
    list_all lpc_model_safe_goal (snd (P!c)) \<and>
    (\<forall>rho m. list_all (lpc_model_goal M)
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c))) \<longrightarrow>
      M (lp_ieval (fst (P!c)) rho)))"

definition lpc_model_goals where
  "lpc_model_goals M K gs eta = (list_all lpc_model_safe_goal gs \<and>
    (\<forall>sigma. list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)
      \<longrightarrow> K (\<lambda>x. lp_isubst (eta x) sigma)))"

fun lpc_model_frame where
  "lpc_model_frame M K (LPCGoals gs,eta)=lpc_model_goals M K gs eta"
| "lpc_model_frame M K (LPCClause gs c m,eta)=lpc_model_goals M K gs eta"
| "lpc_model_frame M K (LPCBarrier m,eta)=True"

lemma lpc_model_replace:
  assumes before: "lpc_model_goals M K gs eta"
    and safe: "list_all lpc_model_safe_goal hs"
    and models: "\<And>tau. list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t tau)) hs) \<Longrightarrow>
      list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) tau)) gs)"
  shows "lpc_model_goals M K hs (\<lambda>x. lp_isubst (eta x) sigma)"
proof (unfold lpc_model_goals_def, intro conjI allI impI)
  show "list_all lpc_model_safe_goal hs" by (rule safe)
next
  fix tau assume after: "list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t tau)) hs)"
  have earlier: "list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t (\<lambda>x. lp_isubst (sigma x) tau))) gs)"
    using models[OF after] by (simp add: lpc_isubst_comp)
  show "K (\<lambda>x. lp_isubst (lp_isubst (eta x) sigma) tau)"
    using before earlier by (auto simp: lpc_model_goals_def lpc_isubst_comp)
qed

lemma lpc_model_resolution:
  assumes program: "lpc_model_program P M" and index: "c<length P"
    and equation: "lp_isubst a sigma=lp_ieval (fst (P!c)) rho"
    and before: "lpc_model_goals M K (LPCAtom a#gs) eta"
  shows "lpc_model_goals M K
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)
    (\<lambda>x. lp_isubst (eta x) sigma)"
proof (rule lpc_model_replace[OF before])
  show "list_all lpc_model_safe_goal
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @ map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
    using program index before by (auto simp: lpc_model_program_def lpc_model_goals_def list_all_iff)
next
  fix tau assume after: "list_all (lpc_model_goal M)
    (map (lp_cut_map (\<lambda>t. lp_isubst t tau))
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @ map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs))"
  have body: "list_all (lpc_model_goal M)
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t (\<lambda>x. lp_isubst (rho x) tau))) (snd (P!c)))"
    using after by (simp add: map_map o_def lpc_model_bind_map lp_ieval_subst)
  have head: "M (lp_ieval (fst (P!c)) (\<lambda>x. lp_isubst (rho x) tau))"
    using program index body by (auto simp: lpc_model_program_def)
  show "list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) tau)) (LPCAtom a#gs))"
    using after head by (simp add: equation lp_ieval_subst map_map o_def lp_cut_map_comp)
qed

lemma lpc_model_unification:
  assumes before: "lpc_model_goals M K (LPCUnify a b#gs) eta"
    and equation: "lp_isubst a sigma=lp_isubst b sigma"
  shows "lpc_model_goals M K (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)
    (\<lambda>x. lp_isubst (eta x) sigma)"
  by (rule lpc_model_replace[OF before])
    (use before equation in \<open>auto simp: lpc_model_goals_def list_all_iff map_map o_def lp_cut_map_comp\<close>)

theorem lpc_model_answer_preserved:
  assumes program: "lpc_model_program P M"
    and step: "lpc_answer_transition P ss event tt"
    and known: "list_all (lpc_model_frame M K) ss"
  shows "list_all (lpc_model_frame M K) tt"
  using step known
proof (cases rule: lpc_answer_transition.cases)
  case (resolve c a gs sigma rho m eta es)
  have equation: "lp_isubst a sigma=lp_ieval (fst (P!c)) rho"
    using resolve by (simp add: lpc_mgu_resolve_def)
  have bound: "c<length P" using resolve by simp
  show ?thesis using resolve known lpc_model_resolution[OF program bound equation] by auto
next
  case (unify a b gs sigma eta es)
  have equation: "lp_isubst a sigma=lp_isubst b sigma"
    using unify by (simp add: lpc_mgu_unify_def)
  show ?thesis using unify known lpc_model_unification[OF _ equation] by auto
qed (use known in \<open>auto simp: lpc_model_goals_def list_all_iff dest: subsetD[OF lpc_answer_prune_subset]\<close>)

lemma lpc_model_answer_event:
  assumes step: "lpc_answer_transition P ss (Some rho) tt"
    and known: "list_all (lpc_model_frame M K) ss"
  shows "K rho"
proof -
  have shape: "ss=(LPCGoals [],rho)#tt" by (rule lpc_answer_event_is_success[OF step])
  have all: "\<forall>sigma. K (\<lambda>x. lp_isubst (rho x) sigma)"
    using known by (simp add: shape lpc_model_goals_def)
  show ?thesis using all[THEN spec, of LPIVar] by simp
qed

lemma lpc_model_builtin:
  assumes before: "lpc_model_goals M K (LPCAtom a#gs) eta"
    and model: "M (lp_isubst a sigma)"
    and stable: "\<And>t tau. M t \<Longrightarrow> M (lp_isubst t tau)"
  shows "lpc_model_goals M K (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)
    (\<lambda>x. lp_isubst (eta x) sigma)"
  by (rule lpc_model_replace[OF before])
    (use before stable[OF model] in \<open>auto simp: lpc_model_goals_def list_all_iff map_map o_def lp_cut_map_comp\<close>)

end
