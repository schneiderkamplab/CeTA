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
       map (\<lambda>(s,t). LPPOEquation s t) (zip (snd (lpp_success_atom_subst h2 mu)) (snd b))))"

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
 let ?eqs = "map (\<lambda>(s,t). LPPOEquation s t) (zip (snd (lpp_success_atom_subst h2 ?mu)) (snd b))"
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
  fix i assume i: "i<length (snd (lpp_success_atom_subst h2 ?mu))" "i<length (snd b)"
  show "lp_ieval (snd (lpp_success_atom_subst h2 ?mu)!i) ?nu=lp_ieval (snd b!i) ?nu"
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


fun lpp_observed_row_short where
 "lpp_observed_row_short k ((h,ps,b,gs),os) = lpp_context_short k (h#b#ps,gs,os)"

fun lpp_observed_rows_connect where
 "lpp_observed_rows_connect ((h,ps,b,gs),os) ((h2,ps2,b2,gs2),os2) =
  (fst b=fst h2 \<and> length (snd b)=length (snd h2))"

lemma lpp_observed_rows_connect_complete:
 assumes first: "(a,middle)\<in>lpp_stable_observed_calls operation {((h,ps,b,gs),os)} P"
 and second: "(middle,z)\<in>lpp_stable_observed_calls operation {((h2,ps2,b2,gs2),os2)} P"
 shows "lpp_observed_rows_connect ((h,ps,b,gs),os) ((h2,ps2,b2,gs2),os2)"
proof -
 obtain eta where first: "middle=lpp_success_atom_eval b eta"
  using first unfolding lpp_stable_observed_calls_def by blast
 obtain tau theta where target: "z=lpp_success_atom_eval b2 theta"
  and second: "lpp_success_iatom_subst middle tau=lpp_success_atom_eval h2 theta"
  using second by (simp only: lpp_stable_observed_calls_def; blast)
 have symbols: "fst b=fst h2"
  using arg_cong[OF second, of fst] by (simp add: first lpp_success_iatom_subst_def lpp_success_atom_eval_def)
 have arity: "length (snd b)=length (snd h2)"
  using arg_cong[OF second, of "\<lambda>a. length (snd a)"]
  by (simp add: first lpp_success_iatom_subst_def lpp_success_atom_eval_def)
 show ?thesis using symbols arity by simp
qed

definition lpp_compose_observed_rows where
 "lpp_compose_observed_rows k D = concat (map (\<lambda>r. map (lpp_compose_observed_row k r) (filter (lpp_observed_rows_connect r) D)) D)"

lemma lpp_composition_calls_mono:
 "D \<subseteq> E \<Longrightarrow> lpp_stable_observed_calls operation D P \<subseteq>
   lpp_stable_observed_calls operation E P"
 unfolding lpp_stable_observed_calls_def by blast

lemma lpp_compose_observed_rows_square:
 assumes short: "list_all (lpp_observed_row_short k) D"
 shows "lpp_stable_observed_calls operation (set D) P O
   lpp_stable_observed_calls operation (set D) P \<subseteq>
   lpp_stable_observed_calls operation (set (lpp_compose_observed_rows k D)) P"
proof
 fix pair assume "pair \<in> lpp_stable_observed_calls operation (set D) P O
   lpp_stable_observed_calls operation (set D) P"
 then obtain a middle z where pair: "pair=(a,z)"
  and first: "(a,middle)\<in>lpp_stable_observed_calls operation (set D) P"
  and second: "(middle,z)\<in>lpp_stable_observed_calls operation (set D) P" by auto
 obtain h ps b gs os where r: "((h,ps,b,gs),os)\<in>set D"
  and edge: "(a,middle)\<in>lpp_stable_observed_calls operation {((h,ps,b,gs),os)} P"
  using first unfolding lpp_stable_observed_calls_def by blast
 obtain h2 ps2 b2 gs2 os2 where r2: "((h2,ps2,b2,gs2),os2)\<in>set D"
  and edge2: "(middle,z)\<in>lpp_stable_observed_calls operation {((h2,ps2,b2,gs2),os2)} P"
  using second unfolding lpp_stable_observed_calls_def by blast
 have small: "lpp_context_short k (h#b#ps,gs,os)"
  using short r by (auto simp: list_all_iff)
 have composed: "(a,z)\<in>lpp_stable_observed_calls operation
   {lpp_compose_observed_row k ((h,ps,b,gs),os) ((h2,ps2,b2,gs2),os2)} P"
  by (rule lpp_compose_observed_row_sound[OF small edge edge2])
 have connects: "lpp_observed_rows_connect ((h,ps,b,gs),os) ((h2,ps2,b2,gs2),os2)"
  by (rule lpp_observed_rows_connect_complete[OF edge edge2])
 have subset: "{lpp_compose_observed_row k ((h,ps,b,gs),os) ((h2,ps2,b2,gs2),os2)}
   \<subseteq> set (lpp_compose_observed_rows k D)"
  proof -
  let ?r = "((h,ps,b,gs),os)"
  let ?s = "((h2,ps2,b2,gs2),os2)"
  have inner: "lpp_compose_observed_row k ?r ?s \<in> set (map (lpp_compose_observed_row k ?r) (filter (lpp_observed_rows_connect ?r) D))"
   unfolding set_map
   by (rule imageI) (use r2 connects in simp)
  have outer: "map (lpp_compose_observed_row k ?r) (filter (lpp_observed_rows_connect ?r) D) \<in>
    set (map (\<lambda>r. map (lpp_compose_observed_row k r) (filter (lpp_observed_rows_connect r) D)) D)"
   using r by (simp only: set_map; rule imageI)
  have member: "lpp_compose_observed_row k ?r ?s \<in> set (lpp_compose_observed_rows k D)"
   unfolding lpp_compose_observed_rows_def set_concat
   by (rule UN_I[where B=set, OF outer inner])
  show ?thesis using member by blast
 qed
 show "pair\<in>lpp_stable_observed_calls operation (set (lpp_compose_observed_rows k D)) P"
  using subsetD[OF lpp_composition_calls_mono[OF subset] composed] pair by simp
qed

lemma lpp_SN_of_square:
 assumes sn: "SN R" and square: "A O A \<subseteq> R"
 shows "SN A"
proof (unfold SN_on_def, intro notI)
 assume "\<exists>f. f 0 \<in> UNIV \<and> chain A f"
 then obtain f where chain: "chain A f" by auto
 have "chain R (\<lambda>n. f (2*n))"
 unfolding chain_def
 proof
  fix n
  have "(f (2*n), f (Suc (2*n)))\<in>A"
   and "(f (Suc (2*n)), f (Suc (Suc (2*n))))\<in>A"
   using chain unfolding chain_def by blast+
  then have "(f (2*n), f (Suc (Suc (2*n))))\<in>R" using square by blast
  then show "(f (2*n), f (2*Suc n))\<in>R" by simp
 qed
 then have "\<not>SN R" by (rule not_SN_onI[OF UNIV_I])
 with sn show False by contradiction
qed

theorem lpp_compose_observed_rows_SN:
 assumes short: "list_all (lpp_observed_row_short k) D"
 and sn: "SN (lpp_stable_observed_calls operation (set (lpp_compose_observed_rows k D)) P)"
 shows "SN (lpp_stable_observed_calls operation (set D) P)"
 by (rule lpp_SN_of_square[OF sn lpp_compose_observed_rows_square[OF short]])

ML \<open>
val checked = [@{thm lpp_compose_observed_row_sound}, @{thm lpp_compose_observed_rows_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted observed row composition" else ();
\<close>
end
