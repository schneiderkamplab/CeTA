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

fun csr_lab_sharp :: "('f,'l) lab \<Rightarrow> ('f,'l) lab" where
  "csr_lab_sharp (Lab f l) = Lab (Sharp f) l"
| "csr_lab_sharp (FunLab f ls) = FunLab (Sharp f) ls"
| "csr_lab_sharp (UnLab f) = Sharp (UnLab f)"
| "csr_lab_sharp (Sharp f) = Sharp (Sharp f)"

lemma unlab_csr_lab_sharp [simp]:
  "unlab (csr_lab_sharp f) = Sharp (unlab f)"
  by (cases f, auto)

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

lemma csdp_step_cond_lift_term:
  assumes image: "map_funs_term U s' = s"
    and marked: "\<And>f us. s = Fun (shp f) us \<Longrightarrow>
      \<exists>f' us'. s' = Fun (shp' f') us' \<and> U f' = f"
    and cond: "csdp_step_cond shp \<mu> p s"
  shows "csdp_step_cond shp' (map_mu U \<mu>) p s'"
  unfolding csdp_step_cond_def
proof (intro allI impI)
  fix p1 j p2
  assume eqposs: "p = p1 @ j # p2 \<and> p \<in> poss s'"
  then have eq: "p = p1 @ j # p2" and pposs': "p \<in> poss s'"
    by auto
  have pposs: "p \<in> poss s"
    using pposs' image by (metis poss_map_funs_term_csr)
  from cond[unfolded csdp_step_cond_def, rule_format,
      OF conjI[OF eq pposs]]
  obtain g us where sub: "s |_ p1 = Fun g us"
    and active: "case p1 of
        [] \<Rightarrow> \<exists>f. g = shp f \<and> j \<in> \<mu> (f,length us)
      | _ \<Rightarrow> j \<in> \<mu> (g,length us)" by blast
  show "\<exists>g' us'. s' |_ p1 = Fun g' us' \<and>
      (case p1 of [] \<Rightarrow> \<exists>f'. g' = shp' f' \<and>
          j \<in> map_mu U \<mu> (f',length us')
        | _ \<Rightarrow> j \<in> map_mu U \<mu> (g',length us'))"
  proof (cases p1)
    case Nil
    from active[simplified Nil] obtain f where g: "g = shp f"
      and j: "j \<in> \<mu> (f,length us)" by auto
    have s: "s = Fun (shp f) us" using sub g unfolding Nil by simp
    from marked[OF s] obtain f' us' where s': "s' = Fun (shp' f') us'"
      and Uf: "U f' = f" by auto
    from arg_cong[OF image, of args] s s'
    have args: "map (map_funs_term U) us' = us" by simp
    from arg_cong[OF args, of length]
    have len: "length us' = length us" by simp
    show ?thesis unfolding Nil s'
      apply (rule exI[where x="shp' f'"])
      apply (rule exI[where x=us'])
      apply (rule conjI)
       apply simp
      apply (simp only: list.case)
      apply (rule exI[where x=f'])
      using j Uf len by (simp add: map_mu_def)
  next
    case (Cons k ks)
    have p1poss': "p1 \<in> poss s'"
      using pposs' eq poss_append_poss by blast
    have mapped_sub: "map_funs_term U (s' |_ p1) = Fun g us"
      using image sub
        subt_at_map_funs_term_csr[of p1 s' U, OF p1poss'] by simp
    then obtain g' us' where sub': "s' |_ p1 = Fun g' us'"
      and Ug: "U g' = g" and len: "length us' = length us"
      by (cases "s' |_ p1", auto)
    have j: "j \<in> \<mu> (g,length us)"
      using active unfolding Cons by simp
    show ?thesis unfolding Cons
      apply (rule exI[where x=g'])
      apply (rule exI[where x=us'])
      apply (rule conjI)
       using sub' apply (simp only: Cons)
      apply (simp only: list.case)
      using j Ug len by (simp add: map_mu_def)
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

locale csr_sl_interpr_same = sl_interpr_same C c I cge lge L LC LD LS
  for C :: "'c set"
  and c :: 'c
  and I :: "('f::{showl,compare_order},'c)inter"
  and cge :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and lge :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
  and L :: "('f,'c,'l)label"
  and LC :: "('f,'l,'f)lcompose"
  and LD :: "('f,'f,'l)ldecompose"
  and LS :: "('f,'l)labels"

context csr_sl_interpr_same
begin

lemma csdp_step_cond_LAB:
  assumes sharp: "\<And>f n l. shp' (LC f n l) = LC (shp f) n l"
    and cond: "csdp_step_cond shp \<mu> p s"
  shows "csdp_step_cond shp' (map_mu UNLAB \<mu>) p (LAB s)"
proof (rule csdp_step_cond_lift_term[where U=UNLAB and s=s
      and shp=shp])
  show "map_funs_term UNLAB (LAB s) = s" by (rule UNLAB_lab)
next
  fix f us
  assume s: "s = Fun (shp f) us"
  let ?clts = "map (eval_lab I L LC default_ass) us"
  show "\<exists>f' us'. LAB s = Fun (shp' f') us' \<and> UNLAB f' = f"
    apply (rule exI[where x="LC f (length us)
        (L (shp f) (map fst ?clts))"])
    apply (rule exI[where x="map snd ?clts"])
    using s sharp[of f "length us" "L (shp f) (map fst ?clts)"] LD_LC
    by (simp add: Let_def)
next
  show "csdp_step_cond shp \<mu> p s" by (rule cond)
qed

end

context sl_interpr_same
begin

lemma hole_pos_eval_lab_ctxt:
  "hole_pos (snd (eval_lab_ctxt \<alpha> d D)) = hole_pos D"
  by (induct D, auto simp: Let_def split: prod.splits)

lemma poss_Lab [simp]: "poss (Lab \<alpha> s) = poss s"
  by (induct s, auto simp: Let_def)

lemma model_rstep_r_p_s_LAB:
  fixes R :: "('f,'v) trs"
  assumes eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and raw: "(s,t) \<in> rstep_r_p_s R (l,r) p \<sigma>"
  shows "\<exists>lr' \<delta>. (LAB s,LAB t) \<in>
    rstep_r_p_s (Lab_trs R) lr' p \<delta>"
proof -
  let ?D = "ctxt_of_pos_term p s"
  from raw have pposs: "p \<in> poss s" and rule: "(l,r) \<in> R"
    and sD: "?D\<langle>l \<cdot> \<sigma>\<rangle> = s"
    and tD: "?D\<langle>r \<cdot> \<sigma>\<rangle> = t"
    unfolding rstep_r_p_s_def Let_def by auto
  have rootstep: "(l \<cdot> \<sigma>,r \<cdot> \<sigma>) \<in> qrstep False {} R"
    by (rule, use rule in auto)
  from quasi_sem_rewrite[OF rootstep model wf_default_ass]
  have eval: "Eval default_ass (l \<cdot> \<sigma>) =
      Eval default_ass (r \<cdot> \<sigma>)" unfolding eq .
  let ?E = "snd (eval_lab_ctxt default_ass
      (Eval default_ass (l \<cdot> \<sigma>)) ?D)"
  have lab_s: "?E\<langle>Lab default_ass (l \<cdot> \<sigma>)\<rangle> = LAB s"
    using sD lab_ctxt[of default_ass ?D "l \<cdot> \<sigma>"] by simp
  have lab_t: "?E\<langle>Lab default_ass (r \<cdot> \<sigma>)\<rangle> = LAB t"
    using tD eval lab_ctxt[of default_ass ?D "r \<cdot> \<sigma>"] by simp
  have hole: "hole_pos ?E = p"
    using hole_pos_eval_lab_ctxt[of default_ass
        "Eval default_ass (l \<cdot> \<sigma>)" ?D]
      hole_pos_ctxt_of_pos_term[OF pposs] by simp
  have ctxt: "ctxt_of_pos_term p (LAB s) = ?E"
    using hole_pos_id_ctxt[OF lab_s] hole by simp
  let ?\<beta> = "subst_ass default_ass \<sigma>"
  let ?\<delta> = "lab_subst default_ass \<sigma>"
  have beta: "wf_ass ?\<beta>" by (rule wf_ass_subst_ass[OF wf_default_ass])
  have lrule: "(Lab ?\<beta> l,Lab ?\<beta> r) \<in> Lab_trs R"
    using rule beta by (simp add: lab_rule_def, force)
  have lsub: "Lab default_ass (l \<cdot> \<sigma>) = Lab ?\<beta> l \<cdot> ?\<delta>"
    by simp
  have rsub: "Lab default_ass (r \<cdot> \<sigma>) = Lab ?\<beta> r \<cdot> ?\<delta>"
    by simp
  have lposs: "p \<in> poss (LAB s)" using pposs by simp
  have source_ctx: "(ctxt_of_pos_term p (LAB s))\<langle>
      Lab ?\<beta> l \<cdot> ?\<delta>\<rangle> = LAB s"
    unfolding ctxt lsub[symmetric] by (rule lab_s)
  have target_ctx: "(ctxt_of_pos_term p (LAB s))\<langle>
      Lab ?\<beta> r \<cdot> ?\<delta>\<rangle> = LAB t"
    unfolding ctxt rsub[symmetric] by (rule lab_t)
  show ?thesis
  proof (intro exI[of _ "(Lab ?\<beta> l,Lab ?\<beta> r)"]
      exI[of _ ?\<delta>])
    show "(LAB s,LAB t) \<in>
        rstep_r_p_s (Lab_trs R) (Lab ?\<beta> l,Lab ?\<beta> r) p ?\<delta>"
      unfolding rstep_r_p_s_def Let_def
      using lposs lrule source_ctx target_ctx by auto
  qed
qed

end

context csr_sl_interpr_same
begin

lemma rrstep_LAB:
  assumes step: "(s,t) \<in> rrstep P"
  shows "(LAB s,LAB t) \<in> rrstep (Lab_trs P)"
  using lab_rqrstep[of s t False "{}" P default_ass]
    step wf_default_ass by simp

lemma model_csdp_step_LAB:
  assumes eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and sharp: "\<And>f n l. shp' (LC f n l) = LC (shp f) n l"
    and step: "(s,t) \<in> csdp_step shp \<mu> R"
  shows "(LAB s,LAB t) \<in>
    csdp_step shp' (map_mu UNLAB \<mu>) (Lab_trs R)"
proof -
  from step obtain p lr \<sigma> where raw:
      "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csdp_step_cond shp \<mu> p s"
    unfolding csdp_step_def csdp_step_p_def by blast
  obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
  from model_rstep_r_p_s_LAB[OF eq model raw[unfolded lr]]
  obtain lr' \<delta> where raw':
      "(LAB s,LAB t) \<in> rstep_r_p_s (Lab_trs R) lr' p \<delta>" by blast
  have cond': "csdp_step_cond shp' (map_mu UNLAB \<mu>) p (LAB s)"
    by (rule csdp_step_cond_LAB[OF sharp cond])
  show ?thesis unfolding csdp_step_def csdp_step_p_def
    using raw' cond' by blast
qed

lemma model_csdp_step_LAB_rstep:
  assumes eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and step: "(s,t) \<in> csdp_step shp \<mu> R"
  shows "(LAB s,LAB t) \<in> rstep (Lab_trs R)"
proof -
  from step obtain p lr \<sigma> where raw:
      "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    unfolding csdp_step_def csdp_step_p_def by blast
  obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
  from model_rstep_r_p_s_LAB[OF eq model raw[unfolded lr]]
  obtain lr' \<delta> where
    "(LAB s,LAB t) \<in> rstep_r_p_s (Lab_trs R) lr' p \<delta>" by blast
  then show ?thesis by (rule rstep_r_p_s_imp_rstep)
qed

lemma map_funs_trs_UNLAB_Lab_trs:
  "map_funs_trs UNLAB (Lab_trs R) \<subseteq> R"
proof
  fix lr'
  assume in_map: "lr' \<in> map_funs_trs UNLAB (Lab_trs R)"
  then obtain llr where llr: "llr \<in> Lab_trs R"
    and lr': "lr' = map_funs_rule UNLAB llr"
    by (auto simp: map_funs_trs.simps)
  from llr obtain lr \<alpha> where lr: "lr \<in> R"
    and llr: "llr = (Lab \<alpha> (fst lr),Lab \<alpha> (snd lr))"
    by (auto simp: lab_rule_def)
  show "lr' \<in> R" unfolding lr' llr
    using lr by (cases lr, simp add: UNLAB_lab)
qed

theorem finite_min_csr_dpp_semantic_labeling:
  assumes fin: "finite_min_csr_dpp shp' (map_mu UNLAB \<mu>)
      (Lab_trs P) (Lab_trs R)"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and sharp: "\<And>f n l. shp' (LC f n l) = LC (shp f) n l"
    and commute: "\<And>f. UNLAB (shp' f) = shp (UNLAB f)"
  shows "finite_min_csr_dpp shp \<mu> P R"
proof (rule finite_min_csr_dpp_map_retract[OF fin commute])
  show "map_funs_trs UNLAB (Lab_trs R) \<subseteq> R"
    by (rule map_funs_trs_UNLAB_Lab_trs)
next
  fix t
  show "map_funs_term UNLAB (LAB t) = t" by (rule UNLAB_lab)
next
  fix s t
  assume "(s,t) \<in> rrstep P"
  then show "(LAB s,LAB t) \<in> rrstep (Lab_trs P)"
    by (rule rrstep_LAB)
next
  fix s t
  assume "(s,t) \<in> csdp_step shp \<mu> R"
  then show "(LAB s,LAB t) \<in>
      csdp_step shp' (map_mu UNLAB \<mu>) (Lab_trs R)"
    by (rule model_csdp_step_LAB[OF eq model sharp])
qed

theorem finite_min_csr_dpp_semantic_labeling_nonminimal:
  assumes fin: "finite_dpp (False,False,Lab_trs P,{},
      {},{},Lab_trs R)"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
  shows "finite_min_csr_dpp shp \<mu> P R"
proof -
  have target: "SN_rel (rrstep (Lab_trs P)) (rstep (Lab_trs R))"
    using fin unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  let ?M = "csr_min_pair_step shp \<mu> P R"
  let ?S = "csdp_step shp \<mu> R"
  have strict: "\<And>s t. (s,t) \<in> ?M \<Longrightarrow>
      (LAB s,LAB t) \<in>
        (rrstep (Lab_trs P) \<union> rstep (Lab_trs R))\<^sup>* O
        rrstep (Lab_trs P) O
        (rrstep (Lab_trs P) \<union> rstep (Lab_trs R))\<^sup>*"
  proof -
    fix s t
    assume "(s,t) \<in> ?M"
    then have "(s,t) \<in> rrstep P"
      unfolding csr_min_pair_step_def by auto
    from rrstep_LAB[OF this]
    show "(LAB s,LAB t) \<in>
        (rrstep (Lab_trs P) \<union> rstep (Lab_trs R))\<^sup>* O
        rrstep (Lab_trs P) O
        (rrstep (Lab_trs P) \<union> rstep (Lab_trs R))\<^sup>*" by auto
  qed
  have weak: "\<And>s t. (s,t) \<in> ?S \<Longrightarrow>
      (LAB s,LAB t) \<in>
        (rrstep (Lab_trs P) \<union> rstep (Lab_trs R))\<^sup>*"
    using model_csdp_step_LAB_rstep[OF eq model] by auto
  from SN_rel_map[where R="?M" and Rw="?S" and R'="rrstep (Lab_trs P)"
      and Rw'="rstep (Lab_trs R)" and f=LAB, OF target strict weak]
  show ?thesis unfolding finite_min_csr_dpp_def .
qed

end

end
