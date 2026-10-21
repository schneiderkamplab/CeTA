theory LP_Mode_Refinement
  imports LP_Infinite_Resolution
begin

text \<open>Predicate copies may have different argument filters.  Erasure changes
only the predicate of an atom, never a data symbol, argument, or substitution.
Every source clause must be represented for every admitted copy of its head.
The condition is independent of the heuristic used to discover the copies.\<close>

definition lp_mode_atom where
  "lp_mode_atom e a = (e (fst a), snd a)"

definition lp_mode_clause where
  "lp_mode_clause e c = (lp_mode_atom e (fst c), map (lp_mode_atom e) (snd c))"

definition lp_mode_cover where
  "lp_mode_cover P Q e modes = (\<forall>f\<in>set modes. \<forall>c\<in>set P.
    e f = fst (fst c) \<longrightarrow> (\<exists>d\<in>set Q.
      fst (fst d) = f \<and> lp_mode_clause e d = c \<and>
      list_all (\<lambda>b. fst b \<in> set modes) (snd d)))"

lemma lp_mode_eval[simp]:
  "lp_mode_atom e (lp_atom_eval a \<rho>) = lp_atom_eval (lp_mode_atom e a) \<rho>"
  by (simp add: lp_mode_atom_def lp_atom_eval_def)

lemma lp_mode_subst[simp]:
  "lp_mode_atom e (lp_iatom_subst a \<sigma>) = lp_iatom_subst (lp_mode_atom e a) \<sigma>"
  by (simp add: lp_mode_atom_def lp_iatom_subst_def)

lemma lp_mode_step:
  assumes cover: "lp_mode_cover P Q e modes"
    and valid: "list_all (\<lambda>a. fst a \<in> set modes) gs"
    and step: "(map (lp_mode_atom e) gs,hs) \<in> lp_ild P"
  obtains ks where "(gs,ks) \<in> lp_ild Q"
    "list_all (\<lambda>a. fst a \<in> set modes) ks"
    "map (lp_mode_atom e) ks = hs"
proof -
  obtain a rest c \<sigma> \<rho> where gs: "gs=a#rest" and c: "c<length P"
    and match: "lp_iatom_subst (lp_mode_atom e a) \<sigma> = lp_atom_eval (fst (P!c)) \<rho>"
    and hs: "hs = map (\<lambda>b. lp_atom_eval b \<rho>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) (map (lp_mode_atom e) rest)"
    using step by (cases gs; cases rule: lp_ild.cases) auto
  have am: "fst a \<in> set modes" and rest: "list_all (\<lambda>a. fst a \<in> set modes) rest"
    using valid gs by simp_all
  have head: "e (fst a) = fst (fst (P!c))"
    using arg_cong[OF match, of fst] by (simp add: lp_iatom_subst_def lp_mode_atom_def lp_atom_eval_def)
  obtain d where d: "d \<in> set Q" and dh: "fst (fst d) = fst a"
    and dc: "lp_mode_clause e d = P!c"
    and dm: "list_all (\<lambda>b. fst b \<in> set modes) (snd d)"
    using cover am nth_mem[OF c] head unfolding lp_mode_cover_def by blast
  obtain i where i: "i<length Q" and qi: "Q!i=d" using d by (metis in_set_conv_nth)
  have args: "snd (fst d) = snd (fst (P!c))"
    using arg_cong[OF dc, of "\<lambda>c. snd (fst c)"]
    by (simp add: lp_mode_clause_def lp_mode_atom_def)
  have mh: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst d) \<rho>"
    using match dh args by (auto simp: lp_mode_atom_def lp_iatom_subst_def lp_atom_eval_def)
  let ?ks = "map (\<lambda>b. lp_atom_eval b \<rho>) (snd d) @ map (\<lambda>b. lp_iatom_subst b \<sigma>) rest"
  have qs: "(gs,?ks) \<in> lp_ild Q"
    using lp_ild.resolve[OF i, of a \<sigma> \<rho> rest] mh by (simp add: gs qi)
  have vm: "list_all (\<lambda>a. fst a \<in> set modes) ?ks"
    using dm rest by (auto simp: list_all_iff lp_atom_eval_def lp_iatom_subst_def)
  have body: "map (lp_mode_atom e) (snd d) = snd (P!c)"
    using arg_cong[OF dc, of snd] by (simp add: lp_mode_clause_def)
  have erased: "map (lp_mode_atom e) ?ks = hs"
    using arg_cong[OF body, of "map (\<lambda>b. lp_atom_eval b \<rho>)"]
    by (simp add: hs o_def)
  show thesis by (rule that[OF qs vm erased])
qed

theorem lp_mode_termination:
  assumes cover: "lp_mode_cover P Q e modes"
    and sn: "SN_on (lp_ild Q) {gs}"
    and valid: "list_all (\<lambda>a. fst a \<in> set modes) gs"
  shows "SN_on (lp_ild P) {map (lp_mode_atom e) gs}"
proof -
  have imp: "list_all (\<lambda>a. fst a \<in> set modes) gs \<longrightarrow>
      SN_on (lp_ild P) {map (lp_mode_atom e) gs}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix xs assume ih: "\<And>ys. (xs,ys) \<in> lp_ild Q \<Longrightarrow>
      list_all (\<lambda>a. fst a \<in> set modes) ys \<longrightarrow>
      SN_on (lp_ild P) {map (lp_mode_atom e) ys}"
    show "list_all (\<lambda>a. fst a \<in> set modes) xs \<longrightarrow>
      SN_on (lp_ild P) {map (lp_mode_atom e) xs}"
    proof
      assume vx: "list_all (\<lambda>a. fst a \<in> set modes) xs"
      show "SN_on (lp_ild P) {map (lp_mode_atom e) xs}"
      proof (rule step_reflects_SN_on)
        fix hs assume step: "(map (lp_mode_atom e) xs,hs) \<in> lp_ild P"
        obtain ys where xy: "(xs,ys) \<in> lp_ild Q"
          and vy: "list_all (\<lambda>a. fst a \<in> set modes) ys"
          and eq: "map (lp_mode_atom e) ys = hs"
          by (rule lp_mode_step[OF cover vx step]) blast
        show "SN_on (lp_ild P) {hs}" using ih[OF xy] vy by (simp add: eq)
      qed
    qed
  qed
  show ?thesis using imp valid by blast
qed

definition lp_check_mode_cover where
  "lp_check_mode_cover P Q aliases = (let
    e = (\<lambda>f. case map_of aliases f of None \<Rightarrow> f | Some g \<Rightarrow> g);
    modes = map fst aliases
    in list_all (\<lambda>f. list_all (\<lambda>c. e f \<noteq> fst (fst c) \<or>
      list_ex (\<lambda>d. fst (fst d) = f \<and> lp_mode_clause e d = c \<and>
        list_all (\<lambda>b. fst b \<in> set modes) (snd d)) Q) P) modes)"

lemma lp_check_mode_cover_sound:
  "lp_check_mode_cover P Q aliases \<Longrightarrow>
    lp_mode_cover P Q (\<lambda>f. case map_of aliases f of None \<Rightarrow> f | Some g \<Rightarrow> g)
      (map fst aliases)"
  by (auto simp: lp_check_mode_cover_def lp_mode_cover_def Let_def list_all_iff list_ex_iff)

end
