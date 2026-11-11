theory LP_Prolog_Stable_Success_Case_Expansion
 imports LP_Prolog_Stable_Success_Cases LP_Prolog_Stable_Fresh_Context
begin

fun lpp_success_case_row where
 "lpp_success_case_row k p ((h,ps,b,gs),os) (ch,bs,cgs) =
   (let mu=lpp_success_case_subst k;
        fresh_guards=map (\<lambda>g. lpp_success_guard_subst g mu) cgs
    in ((h,ps @ map (\<lambda>a. lpp_success_atom_subst a mu) bs,b,gs @ fresh_guards),
      os @ map (\<lambda>(s,t). LPPOEquation s t)
        (zip (snd (lpp_success_atom_subst ch mu)) (snd p)) @
      concat (map lpp_success_case_observations fresh_guards)))"

lemma lpp_success_case_old_atom:
 assumes "list_all (\<lambda>t. \<forall>x\<in>vars_term t. length x<k) (snd a)"
 shows "lpp_success_atom_eval a (lpp_success_case_env k eta theta)=lpp_success_atom_eval a eta"
 using assms by (auto simp: lpp_success_atom_eval_def list_all_iff
   intro!: map_cong lpp_success_case_old_term)

lemma lpp_success_case_old_context:
 assumes "lpp_context_short k ctx"
 shows "lpp_stable_context_holds operation P ctx (lpp_success_case_env k eta theta)=
   lpp_stable_context_holds operation P ctx eta"
 by (rule lpp_stable_context_environment_cong)
   (use assms in \<open>auto simp: lpp_context_short_def list_all_iff intro: lpp_success_case_old_term\<close>)

lemma lpp_success_case_row_sound:
 assumes prefix: "p\<in>set ps"
   and short: "lpp_context_short k (h#b#ps,gs,os)"
 shows "lpp_stable_observed_calls operation {((h,ps,b,gs),os)} P \<subseteq>
   lpp_stable_observed_calls operation
    (set (map (lpp_success_case_row k p ((h,ps,b,gs),os))
      (filter (\<lambda>(ch,bs,cgs). fst ch=fst p \<and> length (snd ch)=length (snd p)) P))) P"
proof
 fix edge
 assume member: "edge\<in>lpp_stable_observed_calls operation {((h,ps,b,gs),os)} P"
 obtain a sigma eta where edge: "edge=(a,lpp_success_atom_eval b eta)"
   and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
   and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
   and observed: "list_all (lpp_stable_observation_holds operation eta) os"
   and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
     (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
   using member by (simp only: lpp_stable_observed_calls_def; blast)
 have success: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval p eta)"
   using helpers prefix by (auto simp: list_all_iff)
 obtain ch bs cgs theta where clause: "(ch,bs,cgs)\<in>set P"
   and name: "fst ch=fst (lpp_success_atom_eval p eta)"
   and arity: "length (snd ch)=length (snd (lpp_success_atom_eval p eta))"
   and head_value: "lpp_success_atom_eval ch theta=lpp_success_atom_eval p eta"
   and clause_guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) theta) cgs"
   and clause_body: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
     (map (\<lambda>g. lpp_success_atom_eval g theta) bs)"
   by (rule lpp_success_cases_complete[OF success]) blast
 let ?nu = "lpp_success_case_env k eta theta"
 let ?mu = "lpp_success_case_subst k"
 let ?fg = "map (\<lambda>g. lpp_success_guard_subst g ?mu) cgs"
 let ?fb = "map (\<lambda>g. lpp_success_atom_subst g ?mu) bs"
 let ?eqs = "map (\<lambda>(s,t). LPPOEquation s t) (zip (snd (lpp_success_atom_subst ch ?mu)) (snd p))"
 have old_atom: "lpp_success_atom_eval x ?nu=lpp_success_atom_eval x eta" if "x\<in>set (h#b#ps)" for x
   by (rule lpp_success_case_old_atom)
     (use short that in \<open>auto simp: lpp_context_short_def list_all_iff\<close>)
 have old_context: "lpp_stable_context_holds operation P (ps,gs,os) ?nu"
 proof -
   have ctx: "lpp_stable_context_holds operation P (ps,gs,os) eta"
     using guards observed helpers by (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff intro: lpp_stable_observation_refines)
   have small: "lpp_context_short k (ps,gs,os)"
     using short by (auto simp: lpp_context_short_def list_all_iff)
   show ?thesis using ctx lpp_success_case_old_context[OF small, of operation P eta theta] by simp
 qed
 have fresh_guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) ?nu) ?fg"
   using clause_guards by (simp add: list_all_iff lpp_success_case_fresh_guard)
 have fresh_body: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
   (map (\<lambda>g. lpp_success_atom_eval g ?nu) ?fb)"
   using clause_body by (simp add: list_all_iff lpp_success_case_fresh_atom)
 have equality: "map (\<lambda>t. lp_ieval t ?nu) (snd (lpp_success_atom_subst ch ?mu))=
   map (\<lambda>t. lp_ieval t ?nu) (snd p)"
   using lpp_success_case_fresh_atom[of ch k eta theta] head_value old_atom[of p] prefix
   by (simp add: lpp_success_atom_eval_def)
 have each_equation: "lp_ieval (snd (lpp_success_atom_subst ch ?mu)!i) ?nu=lp_ieval (snd p!i) ?nu"
   if "i<length (snd (lpp_success_atom_subst ch ?mu))" "i<length (snd p)" for i
   using arg_cong[OF equality, of "\<lambda>xs. xs!i"] that by simp
 have equations: "list_all (lpp_stable_observation_holds operation ?nu) ?eqs"
   using each_equation by (auto simp: list_all_iff set_zip)
 have observations: "list_all (lpp_stable_observation_holds operation ?nu)
   (concat (map lpp_success_case_observations ?fg))"
   using fresh_guards lpp_success_case_observations_sound by (fastforce simp: list_all_iff)
 have covered: "lpp_success_case_row k p ((h,ps,b,gs),os) (ch,bs,cgs)\<in>
   set (map (lpp_success_case_row k p ((h,ps,b,gs),os))
      (filter (\<lambda>(ch,bs,cgs). fst ch=fst p \<and> length (snd ch)=length (snd p)) P))"
 proof -
   have selected: "(ch,bs,cgs)\<in>set (filter (\<lambda>(ch,bs,cgs). fst ch=fst p \<and> length (snd ch)=length (snd p)) P)"
     using clause name arity by (auto simp: lpp_success_atom_eval_def)
   show ?thesis using imageI[OF selected, of "lpp_success_case_row k p ((h,ps,b,gs),os)"]
     by (simp only: set_map)
 qed
 show "edge\<in>lpp_stable_observed_calls operation
    (set (map (lpp_success_case_row k p ((h,ps,b,gs),os))
      (filter (\<lambda>(ch,bs,cgs). fst ch=fst p \<and> length (snd ch)=length (snd p)) P))) P"
   unfolding edge lpp_stable_observed_calls_def
   apply (rule CollectI)
   apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ "ps @ ?fb"], rule exI[of _ b],
     rule exI[of _ "gs @ ?fg"], rule exI[of _ "os @ ?eqs @ concat (map lpp_success_case_observations ?fg)"],
     rule exI[of _ sigma], rule exI[of _ ?nu])
   using covered old_context fresh_guards fresh_body equations observations matching old_atom[of h] old_atom[of b]
   by (auto simp: lpp_success_case_row.simps Let_def lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_success_case_row_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted successful-helper expansion dependency" else ();
\<close>
end
