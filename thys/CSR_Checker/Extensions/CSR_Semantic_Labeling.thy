(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Semantic_Labeling
  imports CSR_Minimal_CSDP_Proofs
begin

text \<open>
  Infrastructure for a context-sensitive semantic-labeling processor.  The
  replacement map on the labeled signature is obtained by forgetting one
  symbol layer.  These mapping lemmas are deliberately independent of the
  concrete labeling algebra, so the executable checker can reuse them for
  finite semantic labels as well as future typed labels.
\<close>

definition map_mu :: "('g \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> 'g mu" where
  "map_mu h \<mu> = (\<lambda>(g,n). \<mu> (h g,n))"

lemma poss_map_funs_term_csr [simp]:
  "poss (map_funs_term h t) = poss t"
  by (induct t, auto)

lemma subt_at_map_funs_term_csr:
  assumes p: "p \<in> poss t"
  shows "map_funs_term h t |_ p = map_funs_term h (t |_ p)"
  using p
proof (induct p arbitrary: t)
  case Nil
  show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts"
    and pp: "p \<in> poss (ts ! i)" by (cases t, auto)
  show ?case unfolding t using Cons.hyps[OF pp] i by simp
qed

lemma replace_at_map_funs_term_csr:
  assumes p: "p \<in> poss t"
  shows "map_funs_term h (replace_at t p u) =
    replace_at (map_funs_term h t) p (map_funs_term h u)"
  using p
proof (induct p arbitrary: t)
  case Nil
  show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts"
    and pp: "p \<in> poss (ts ! i)" by (cases t, auto)
  show ?case unfolding t using Cons.hyps[OF pp] i
    by (simp add: upd_conv_take_nth_drop take_map drop_map)
qed

lemma csstep_cond_map_funs_term:
  assumes cond: "csstep_cond (map_mu h \<mu>) p s"
  shows "csstep_cond \<mu> p (map_funs_term h s)"
proof -
  show ?thesis unfolding csstep_cond_def
  proof (intro allI impI)
    fix p1 i p2
    assume at: "p = p1 @ i # p2 \<and> p \<in> poss (map_funs_term h s)"
    from at have eq: "p = p1 @ i # p2" and pposs: "p \<in> poss s"
      by auto
    from cond[unfolded csstep_cond_def, rule_format,
        OF conjI[OF eq pposs]]
    obtain f ts where sub: "s |_ p1 = Fun f ts"
      and active: "i \<in> map_mu h \<mu> (f,length ts)" by blast
    have p1poss: "p1 \<in> poss s"
      using pposs eq poss_append_poss by blast
    show "\<exists>g us. map_funs_term h s |_ p1 = Fun g us \<and>
        i \<in> \<mu> (g,length us)"
    proof (intro exI[of _ "h f"]
        exI[of _ "map (map_funs_term h) ts"] conjI)
      show "map_funs_term h s |_ p1 = Fun (h f) (map (map_funs_term h) ts)"
        unfolding subt_at_map_funs_term_csr[OF p1poss] sub by simp
      show "i \<in> \<mu> (h f,length (map (map_funs_term h) ts))"
        using active unfolding map_mu_def by simp
    qed
  qed
qed

lemma rstep_r_p_s_map_funs_term:
  assumes step: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
  shows "(map_funs_term h s,map_funs_term h t) \<in>
    rstep_r_p_s (map_funs_trs h R) (map_funs_rule h lr) p
      (map_funs_subst h \<sigma>)"
proof -
  from step have p: "p \<in> poss s" and lr: "lr \<in> R"
    and at: "s |_ p = fst lr \<cdot> \<sigma>"
    and t: "t = replace_at s p (snd lr \<cdot> \<sigma>)"
    unfolding rstep_r_p_s_def' by auto
  have mapped_at: "map_funs_term h s |_ p =
      fst (map_funs_rule h lr) \<cdot> map_funs_subst h \<sigma>"
    by (simp only: subt_at_map_funs_term_csr[OF p] at
      map_funs_subst_distrib map_funs_rule.simps prod.sel)
  have mapped_t: "map_funs_term h t = replace_at (map_funs_term h s) p
      (snd (map_funs_rule h lr) \<cdot> map_funs_subst h \<sigma>)"
    by (simp only: t replace_at_map_funs_term_csr[OF p]
      map_funs_subst_distrib map_funs_rule.simps prod.sel)
  show ?thesis using p lr mapped_at mapped_t
    unfolding rstep_r_p_s_def' map_funs_trs.simps by auto
qed

lemma csstep_map_funs_term:
  assumes step: "(s,t) \<in> csstep (map_mu h \<mu>) R"
  shows "(map_funs_term h s,map_funs_term h t) \<in>
    csstep \<mu> (map_funs_trs h R)"
proof -
  from step obtain p lr \<sigma> where raw:
      "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond (map_mu h \<mu>) p s"
    unfolding csstep_def csstep_p_def by blast
  have mapped_raw: "(map_funs_term h s,map_funs_term h t) \<in>
      rstep_r_p_s (map_funs_trs h R) (map_funs_rule h lr) p
        (map_funs_subst h \<sigma>)"
    by (rule rstep_r_p_s_map_funs_term[OF raw])
  have mapped_cond: "csstep_cond \<mu> p (map_funs_term h s)"
    by (rule csstep_cond_map_funs_term[OF cond])
  show ?thesis unfolding csstep_def csstep_p_def
    using mapped_raw mapped_cond by blast
qed

lemma csstep_mono_rules:
  assumes sub: "R \<subseteq> S"
  shows "csstep \<mu> R \<subseteq> csstep \<mu> S"
proof
  fix st
  assume "st \<in> csstep \<mu> R"
  then obtain s t p lr \<sigma> where st: "st = (s,t)"
    and raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p s"
    unfolding csstep_def csstep_p_def by blast
  from raw have "(s,t) \<in> rstep_r_p_s S lr p \<sigma>"
    using sub unfolding rstep_r_p_s_def' by auto
  with cond show "st \<in> csstep \<mu> S"
    unfolding st csstep_def csstep_p_def by blast
qed

lemma SN_on_via_term_map:
  assumes mapped: "\<And>s t. (s,t) \<in> A \<Longrightarrow> (h s,h t) \<in> B"
    and sn: "SN_on B {h s}"
  shows "SN_on A {s}"
proof (rule SN_onI)
  fix f
  assume start: "f 0 \<in> {s}" and steps: "chain A f"
  let ?g = "h \<circ> f"
  have g0: "?g 0 \<in> {h s}" using start by simp
  have mapped_steps: "\<forall>i. (?g i,?g (Suc i)) \<in> B"
  proof
    fix i
    from steps have "(f i,f (Suc i)) \<in> A"
      unfolding chain_def by simp
    from mapped[OF this]
    show "(?g i,?g (Suc i)) \<in> B" by simp
  qed
  have chain: "chain B ?g"
    using mapped_steps unfolding chain_def .
  from not_SN_onI[OF g0 chain]
  have "\<not> SN_on B {h s}" .
  with sn show False by contradiction
qed

lemma SN_on_csstep_map_funs_term:
  assumes rules: "map_funs_trs h R \<subseteq> S"
    and sn: "SN_on (csstep \<mu> S) {map_funs_term h s}"
  shows "SN_on (csstep (map_mu h \<mu>) R) {s}"
proof (rule SN_on_via_term_map[
    where A="csstep (map_mu h \<mu>) R" and B="csstep \<mu> S"
      and h="map_funs_term h" and s=s, OF _ sn])
  fix x y
  assume step: "(x,y) \<in> csstep (map_mu h \<mu>) R"
  from csstep_map_funs_term[OF step]
  show "(map_funs_term h x,map_funs_term h y) \<in> csstep \<mu> S"
    using csstep_mono_rules[OF rules] by blast
qed

lemma csdp_step_cond_map_funs_term:
  assumes commute: "\<And>f. h (shp' f) = shp (h f)"
    and cond: "csdp_step_cond shp' (map_mu h \<mu>) p s"
  shows "csdp_step_cond shp \<mu> p (map_funs_term h s)"
  unfolding csdp_step_cond_def
proof (intro allI impI)
  fix p1 j p2
  assume eqposs: "p = p1 @ j # p2 \<and> p \<in> poss (map_funs_term h s)"
  then have eq: "p = p1 @ j # p2" and pposs: "p \<in> poss s" by auto
  from cond[unfolded csdp_step_cond_def, rule_format, OF conjI[OF eq pposs]]
  obtain g us where sub: "s |_ p1 = Fun g us"
    and active: "case p1 of
        [] \<Rightarrow> \<exists>f. g = shp' f \<and> j \<in> map_mu h \<mu> (f,length us)
      | _ \<Rightarrow> j \<in> map_mu h \<mu> (g,length us)" by blast
  have p1poss: "p1 \<in> poss s"
    using pposs eq poss_append_poss by blast
  have mapped_sub: "map_funs_term h s |_ p1 =
      Fun (h g) (map (map_funs_term h) us)"
    unfolding subt_at_map_funs_term_csr[OF p1poss] sub by simp
  show "\<exists>g us. map_funs_term h s |_ p1 = Fun g us \<and>
      (case p1 of [] \<Rightarrow> \<exists>f. g = shp f \<and> j \<in> \<mu> (f,length us)
        | _ \<Rightarrow> j \<in> \<mu> (g,length us))"
  proof (intro exI[of _ "h g"]
      exI[of _ "map (map_funs_term h) us"] conjI)
    show "map_funs_term h s |_ p1 =
        Fun (h g) (map (map_funs_term h) us)" by (rule mapped_sub)
    show "case p1 of [] \<Rightarrow> \<exists>f. h g = shp f \<and>
          j \<in> \<mu> (f,length (map (map_funs_term h) us))
        | _ \<Rightarrow> j \<in> \<mu> (h g,length (map (map_funs_term h) us))"
      using active commute unfolding map_mu_def
      by (cases p1, auto split: prod.splits)
  qed
qed

lemma csdp_step_map_funs_term:
  assumes commute: "\<And>f. h (shp' f) = shp (h f)"
    and step: "(s,t) \<in> csdp_step shp' (map_mu h \<mu>) R"
  shows "(map_funs_term h s,map_funs_term h t) \<in>
    csdp_step shp \<mu> (map_funs_trs h R)"
proof -
  from step obtain p lr \<sigma> where raw:
      "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csdp_step_cond shp' (map_mu h \<mu>) p s"
    unfolding csdp_step_def csdp_step_p_def by blast
  have mapped_raw: "(map_funs_term h s,map_funs_term h t) \<in>
      rstep_r_p_s (map_funs_trs h R) (map_funs_rule h lr) p
        (map_funs_subst h \<sigma>)"
    by (rule rstep_r_p_s_map_funs_term[OF raw])
  have mapped_cond: "csdp_step_cond shp \<mu> p (map_funs_term h s)"
    by (rule csdp_step_cond_map_funs_term[OF commute cond])
  show ?thesis unfolding csdp_step_def csdp_step_p_def
    using mapped_raw mapped_cond by blast
qed

lemma SN_on_csdp_step_map_funs_term:
  assumes commute: "\<And>f. h (shp' f) = shp (h f)"
    and rules: "map_funs_trs h R \<subseteq> S"
    and sn: "SN_on (csdp_step shp \<mu> S) {map_funs_term h s}"
  shows "SN_on (csdp_step shp' (map_mu h \<mu>) R) {s}"
proof (rule SN_on_via_term_map[
    where A="csdp_step shp' (map_mu h \<mu>) R"
      and B="csdp_step shp \<mu> S" and h="map_funs_term h" and s=s,
      OF _ sn])
  fix x y
  assume step: "(x,y) \<in> csdp_step shp' (map_mu h \<mu>) R"
  from csdp_step_map_funs_term[OF commute step]
  show "(map_funs_term h x,map_funs_term h y) \<in> csdp_step shp \<mu> S"
    using csdp_step_mono[OF rules] by blast
qed

theorem finite_min_csr_dpp_map:
  fixes P R :: "('f::{showl,compare_order},'v) trs"
    and P' R' :: "('f,'v) trs"
  assumes fin: "finite_min_csr_dpp shp' \<mu>' P' R'"
    and pair_map: "\<And>s t. (s,t) \<in> rrstep P \<Longrightarrow>
      (F s,F t) \<in> rrstep P'"
    and weak_map: "\<And>s t. (s,t) \<in> csdp_step shp \<mu> R \<Longrightarrow>
      (F s,F t) \<in> csdp_step shp' \<mu>' R'"
    and min_map: "\<And>t. SN_on (csdp_step shp \<mu> R) {t} \<Longrightarrow>
      SN_on (csdp_step shp' \<mu>' R') {F t}"
  shows "finite_min_csr_dpp shp \<mu> P R"
proof -
  let ?M = "csr_min_pair_step shp \<mu> P R"
  let ?S = "csdp_step shp \<mu> R"
  let ?M' = "csr_min_pair_step shp' \<mu>' P' R'"
  let ?S' = "csdp_step shp' \<mu>' R'"
  have strict: "\<And>s t. (s,t) \<in> ?M \<Longrightarrow>
      (F s,F t) \<in> (?M' \<union> ?S')\<^sup>* O ?M' O (?M' \<union> ?S')\<^sup>*"
  proof -
    fix s t
    assume st: "(s,t) \<in> ?M"
    then have pair: "(s,t) \<in> rrstep P"
      and minimal: "SN_on ?S {t}"
      unfolding csr_min_pair_step_def by auto
    have "(F s,F t) \<in> ?M'"
      using pair_map[OF pair] min_map[OF minimal]
      unfolding csr_min_pair_step_def by auto
    then show "(F s,F t) \<in>
        (?M' \<union> ?S')\<^sup>* O ?M' O (?M' \<union> ?S')\<^sup>*" by auto
  qed
  have weak: "\<And>s t. (s,t) \<in> ?S \<Longrightarrow>
      (F s,F t) \<in> (?M' \<union> ?S')\<^sup>*"
    using weak_map by auto
  from fin have "SN_rel ?M' ?S'"
    unfolding finite_min_csr_dpp_def .
  from SN_rel_map[where R="?M" and Rw="?S" and R'="?M'" and Rw'="?S'"
      and f=F, OF this strict weak]
  show ?thesis unfolding finite_min_csr_dpp_def .
qed

corollary finite_min_csr_dpp_map_retract:
  fixes P R P' R' :: "('f::{showl,compare_order},'v) trs"
  assumes fin: "finite_min_csr_dpp shp' (map_mu U \<mu>) P' R'"
    and commute: "\<And>f. U (shp' f) = shp (U f)"
    and rules: "map_funs_trs U R' \<subseteq> R"
    and retract: "\<And>t. map_funs_term U (F t) = t"
    and pair_map: "\<And>s t. (s,t) \<in> rrstep P \<Longrightarrow>
      (F s,F t) \<in> rrstep P'"
    and weak_map: "\<And>s t. (s,t) \<in> csdp_step shp \<mu> R \<Longrightarrow>
      (F s,F t) \<in> csdp_step shp' (map_mu U \<mu>) R'"
  shows "finite_min_csr_dpp shp \<mu> P R"
proof (rule finite_min_csr_dpp_map[OF fin pair_map weak_map])
  fix t
  assume sn: "SN_on (csdp_step shp \<mu> R) {t}"
  have sn': "SN_on (csdp_step shp \<mu> R)
      {map_funs_term U (F t)}" using sn retract by simp
  show "SN_on (csdp_step shp' (map_mu U \<mu>) R') {F t}"
    by (rule SN_on_csdp_step_map_funs_term[OF commute rules sn'])
qed

end
