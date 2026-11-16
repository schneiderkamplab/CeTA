theory LP_Prolog_Stable_Success_Cases
 imports LP_Prolog_Stable_Observed_Calls LP_Source_Tree
begin

text \<open>Case analysis concerns actual successful helper derivations. All
matching clauses remain obligations, including recursive premises. This does
not assume helper termination or interpret an opaque success guard.\<close>

fun lpp_success_case_observations where
  "lpp_success_case_observations (LPPSInteger t) = [LPPOInteger t]"
| "lpp_success_case_observations (LPPSEvaluates e t) = [LPPOEvaluation e t]"
| "lpp_success_case_observations (LPPSOpaque t) = []"
| "lpp_success_case_observations (LPPSNumeric c a b) = []"

lemma lpp_success_case_observations_sound:
  "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta g \<Longrightarrow>
    list_all (lpp_stable_observation_holds operation eta) (lpp_success_case_observations g)"
  by (cases g) auto

definition lpp_success_case_subst where
  "lpp_success_case_subst k x = Var (lp_prefix k x)"

definition lpp_success_case_env where
  "lpp_success_case_env k eta theta x = (if length x<k then eta x else theta (drop k x))"

lemma lpp_success_case_old_term:
  assumes "\<forall>x\<in>vars_term t. length x<k"
  shows "lp_ieval t (lpp_success_case_env k eta theta)=lp_ieval t eta"
  by (rule lp_ieval_cong) (use assms in \<open>simp add: lpp_success_case_env_def\<close>)

lemma lpp_success_case_fresh_atom:
  "lpp_success_atom_eval (lpp_success_atom_subst a (lpp_success_case_subst k))
      (lpp_success_case_env k eta theta)=lpp_success_atom_eval a theta"
  by (simp add: lpp_success_atom_subst_eval lpp_success_case_subst_def
    lpp_success_case_env_def lp_prefix_def)

lemma lpp_success_case_fresh_guard:
  "lpp_success_guard_holds E (lpp_success_case_env k eta theta)
      (lpp_success_guard_subst g (lpp_success_case_subst k)) = lpp_success_guard_holds E theta g"
  by (simp add: lpp_success_guard_subst_eval lpp_success_case_subst_def
    lpp_success_case_env_def lp_prefix_def)

lemma lpp_success_cases_complete:
  assumes success: "lpp_guarded_success P E a"
  obtains h bs gs theta where "(h,bs,gs)\<in>set P"
    "fst h=fst a" "length (snd h)=length (snd a)"
    "lpp_success_atom_eval h theta=a"
    "list_all (lpp_success_guard_holds E theta) gs"
    "list_all (lpp_guarded_success P E) (map (\<lambda>b. lpp_success_atom_eval b theta) bs)"
proof -
  obtain h bs gs theta where member: "(h,bs,gs)\<in>set P"
    and head_value: "lpp_success_atom_eval h theta=a"
    and guards: "list_all (lpp_success_guard_holds E theta) gs"
    and body: "list_all (lpp_guarded_success P E) (map (\<lambda>b. lpp_success_atom_eval b theta) bs)"
    using success by (cases rule: lpp_guarded_success.cases) blast
  have predicate: "fst h=fst a" and arity: "length (snd h)=length (snd a)"
    using head_value by (auto simp: lpp_success_atom_eval_def)
  show thesis by (rule that[OF member predicate arity head_value guards body])
qed

ML \<open>
val checked = [@{thm lpp_success_case_observations_sound},
 @{thm lpp_success_case_old_term}, @{thm lpp_success_case_fresh_atom},
 @{thm lpp_success_case_fresh_guard}, @{thm lpp_success_cases_complete}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted successful-helper case dependency" else ();
\<close>
end
