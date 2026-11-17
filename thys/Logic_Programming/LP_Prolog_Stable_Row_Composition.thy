theory LP_Prolog_Stable_Row_Composition
 imports LP_Prolog_Stable_Success_Case_Expansion
begin

text \<open>Composition retains both successful-prefix obligations and all
observations. The intermediate interface is a rational equation, never an
occurs-check-based omission of a potentially cyclic match.\<close>

fun lpp_compose_observed_row where
 "lpp_compose_observed_row k ((h,ps,b,gs),os) ((h2,ps2,b2,gs2),os2) =
   (let mu=lpp_success_case_subst k in
    ((h,ps @ map (\<lambda>p. lpp_success_atom_subst p mu) ps2,
       lpp_success_atom_subst b2 mu, gs @ map (\<lambda>g. lpp_success_guard_subst g mu) gs2),
     os @ map (\<lambda>obs. lpp_numeric_observation_substitute obs mu) os2 @
       map (\<lambda>(s,t). LPPOEquation s t) (zip (snd b) (snd (lpp_success_atom_subst h2 mu)))))"

lemma lpp_success_case_fresh_observation:
 "lpp_stable_observation_holds operation (lpp_success_case_env k eta theta)
   (lpp_numeric_observation_substitute observation (lpp_success_case_subst k)) =
   lpp_stable_observation_holds operation theta observation"
 by (simp add: lpp_stable_observation_substitute lpp_success_case_subst_def
   lpp_success_case_env_def lp_prefix_def)

lemma lpp_compose_observed_row_sound:
 assumes short: "lpp_context_short k (h#b#ps,gs,os)"
   and first: "(a,middle)\<in>lpp_stable_observed_calls operation {((h,ps,b,gs),os)} P"
   and second: "(middle,z)\<in>lpp_stable_observed_calls operation {((h2,ps2,b2,gs2),os2)} P"
 shows "(a,z)\<in>lpp_stable_observed_calls operation
   {lpp_compose_observed_row k ((h,ps,b,gs),os) ((h2,ps2,b2,gs2),os2)} P"
proof -
 obtain sigma eta where middle: "middle=lpp_success_atom_eval b eta"
   and match1: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
   and gs: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
   and os: "list_all (lpp_stable_observation_holds operation eta) os"
   and ps: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>p. lpp_success_atom_eval p eta) ps)"
   using first by (simp only: lpp_stable_observed_calls_def; blast)
 obtain tau theta where target: "z=lpp_success_atom_eval b2 theta"
   and match2: "lpp_success_iatom_subst middle tau=lpp_success_atom_eval h2 theta"
   and gs2: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) theta) gs2"
   and os2: "list_all (lpp_stable_observation_holds operation theta) os2"
   and ps2: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>p. lpp_success_atom_eval p theta) ps2)"
   using second by (simp only: lpp_stable_observed_calls_def; blast)
 let ?eta = "\<lambda>x. lp_isubst (eta x) tau"
 let ?nu = "lpp_success_case_env k ?eta theta"
 let ?mu = "lpp_success_case_subst k"
 let ?sigma = "\<lambda>x. lp_isubst (sigma x) tau"
 let ?fp = "map (\<lambda>p. lpp_success_atom_subst p ?mu) ps2"
 let ?fg = "map (\<lambda>g. lpp_success_guard_subst g ?mu) gs2"
 let ?fo = "map (\<lambda>obs. lpp_numeric_observation_substitute obs ?mu) os2"
 let ?eqs = "map (\<lambda>(s,t). LPPOEquation s t) (zip (snd b) (snd (lpp_success_atom_subst h2 ?mu)))"
 have initial: "lpp_stable_context_holds operation P (ps,gs,os) eta"
   using ps gs os by (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def
      list_all_iff intro: lpp_stable_observation_refines)
 have substituted: "lpp_stable_context_holds operation P (ps,gs,os) ?eta"
   by (rule lpp_stable_context_runtime_subst[OF initial])
 have small: "lpp_context_short k (ps,gs,os)"
   using short by (auto simp: lpp_context_short_def list_all_iff)
 have old_context: "lpp_stable_context_holds operation P (ps,gs,os) ?nu"
   using substituted lpp_success_case_old_context[OF small, of operation P ?eta theta] by simp
 have old_atom: "lpp_success_atom_eval p ?nu=lpp_success_atom_eval p ?eta"
   if "p\<in>set (h#b#ps)" for p
   by (rule lpp_success_case_old_atom)
     (use short that in \<open>auto simp: lpp_context_short_def list_all_iff\<close>)
 have fresh_prefix: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
     (map (\<lambda>p. lpp_success_atom_eval p ?nu) ?fp)"
   using ps2 by (simp add: list_all_iff lpp_success_case_fresh_atom)
 have fresh_guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) ?nu) ?fg"
   using gs2 by (simp add: list_all_iff lpp_success_case_fresh_guard)
 have fresh_observations: "list_all (lpp_stable_observation_holds operation ?nu) ?fo"
   using os2 by (simp add: list_all_iff lpp_success_case_fresh_observation)
 have bridge: "lpp_success_atom_eval b ?eta=lpp_success_atom_eval h2 theta"
   using match2 by (simp add: middle lpp_success_iatom_subst_def lpp_success_atom_eval_def
      map_map lp_ieval_subst o_def)
 have atoms: "lpp_success_atom_eval b ?nu =
     lpp_success_atom_eval (lpp_success_atom_subst h2 ?mu) ?nu"
   using old_atom[of b] bridge lpp_success_case_fresh_atom[of h2 k ?eta theta] by simp
 have equality: "map (\<lambda>t. lp_ieval t ?nu) (snd b)=
     map (\<lambda>t. lp_ieval t ?nu) (snd (lpp_success_atom_subst h2 ?mu))"
   using arg_cong[OF atoms, of snd] by (simp only: lpp_success_atom_eval_def snd_conv)
 have equations: "list_all (lpp_stable_observation_holds operation ?nu) ?eqs"
 proof (auto simp: list_all_iff set_zip)
  fix i assume i: "i<length (snd b)" "i<length (snd (lpp_success_atom_subst h2 ?mu))"
  show "lp_ieval (snd b!i) ?nu=lp_ieval (snd (lpp_success_atom_subst h2 ?mu)!i) ?nu"
   using arg_cong[OF equality, of "\<lambda>xs. xs!i"] i by simp
 qed
 have matching: "lpp_success_iatom_subst a ?sigma=lpp_success_atom_eval h ?nu"
   using arg_cong[OF match1, of "\<lambda>x. lpp_success_iatom_subst x tau"] old_atom[of h]
   by (simp add: lpp_success_iatom_subst_def lpp_success_atom_eval_def map_map
      lp_ieval_subst lp_seg_isubst_comp o_def)
 have result_atom: "lpp_success_atom_eval (lpp_success_atom_subst b2 ?mu) ?nu=z"
   by (simp add: lpp_success_case_fresh_atom target)
 show ?thesis unfolding lpp_stable_observed_calls_def
   apply (rule CollectI)
   apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ "ps @ ?fp"],
     rule exI[of _ "lpp_success_atom_subst b2 ?mu"], rule exI[of _ "gs @ ?fg"],
     rule exI[of _ "os @ ?fo @ ?eqs"], rule exI[of _ ?sigma], rule exI[of _ ?nu])
   using old_context fresh_prefix fresh_guards fresh_observations equations matching result_atom
   by (auto simp: lpp_compose_observed_row.simps Let_def lpp_stable_context_holds_def
      lpp_evaluation_context_holds_def list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_compose_observed_row_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted observed row composition" else ();
\<close>
end
