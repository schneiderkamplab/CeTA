(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Extended_Basic
  imports CSR_Muterm_Ext.CSR_Muterm_Usable_Rules
begin

text \<open>
  Reduction-pair facts for a typed MU-TERM macro step.  They are kept in a
  child session while the extended-basic interpretation is developed so the
  large, stable MU-TERM heap remains reusable between proof iterations.
\<close>

lemma muterm_typed_pair_step_redpair_orientation:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pairs: "P \<subseteq> Rgt \<union> Rge"
    and bridges: "B \<subseteq> Rge"
  shows "muterm_typed_pair_step P B \<subseteq> Rgt \<union> Rge"
proof
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  fix st
  assume step: "st \<in> muterm_typed_pair_step P B"
  obtain s t where st: "st = (s,t)" by (cases st)
  from step have cases:
      "muterm_noncollapsing_rrstep P s t \<or>
       (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
    unfolding st muterm_typed_pair_step_def by auto
  from cases show "st \<in> Rgt \<union> Rge"
  proof
    assume nc: "muterm_noncollapsing_rrstep P s t"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    from pairs pair have order: "(l,r) \<in> Rgt \<union> Rge" by auto
    have "(s,t) \<in> Rgt \<union> Rge"
    proof (cases "(l,r) \<in> Rgt")
      case True
      then have "(s,t) \<in> Rgt" unfolding s t
        by (rule subst.closedD[OF rp.subst_S])
      then show ?thesis by simp
    next
      case False
      with order have "(l,r) \<in> Rge" by auto
      then have "(s,t) \<in> Rge" unfolding s t
        by (rule subst.closedD[OF rp.subst_NS])
      then show ?thesis by simp
    qed
    then show ?thesis unfolding st .
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
    then obtain x l y \<sigma> where pair: "(l,Var y) \<in> P"
      and s: "s = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      and bridge: "(x,t) \<in> rrstep B"
      unfolding muterm_collapsing_rrstep_def by auto
    from bridge obtain a b \<tau> where ab: "(a,b) \<in> B"
      and x': "x = a \<cdot> \<tau>" and t: "t = b \<cdot> \<tau>"
      unfolding rrstep_def' by auto
    from bridges ab have ab_order: "(a,b) \<in> Rge" by auto
    have xt: "(x,t) \<in> Rge" unfolding x' t
      by (rule subst.closedD[OF rp.subst_NS ab_order])
    from pairs pair have order: "(l,Var y) \<in> Rgt \<union> Rge" by auto
    show ?thesis
    proof (cases "(l,Var y) \<in> Rgt")
      case True
      then have inst: "(l \<cdot> \<sigma>,Var y \<cdot> \<sigma>) \<in> Rgt"
        by (rule subst.closedD[OF rp.subst_S])
      have sx: "(s,x) \<in> Rgt" unfolding s x using inst by simp
      from rp.compat_S_NS sx xt have "(s,t) \<in> Rgt" by auto
      then show ?thesis unfolding st by simp
    next
      case False
      with order have lr: "(l,Var y) \<in> Rge" by auto
      have inst: "(l \<cdot> \<sigma>,Var y \<cdot> \<sigma>) \<in> Rge"
        by (rule subst.closedD[OF rp.subst_NS lr])
      have sx: "(s,x) \<in> Rge" unfolding s x using inst by simp
      from rp.trans_NS_point[OF sx xt] show ?thesis unfolding st by simp
    qed
  qed
qed

lemma muterm_typed_pair_step_redpair_residual:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and bridges: "B \<subseteq> Rge"
  shows "muterm_typed_pair_step P B - Rgt \<subseteq>
    muterm_typed_pair_step (P - Rgt) B"
proof
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  fix st
  assume mem: "st \<in> muterm_typed_pair_step P B - Rgt"
  obtain s t where st: "st = (s,t)" by (cases st)
  from mem have step: "(s,t) \<in> muterm_typed_pair_step P B"
    and not_strict: "(s,t) \<notin> Rgt" unfolding st by auto
  from step have cases:
      "muterm_noncollapsing_rrstep P s t \<or>
       (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by auto
  from cases show "st \<in> muterm_typed_pair_step (P - Rgt) B"
  proof
    assume nc: "muterm_noncollapsing_rrstep P s t"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and rhs: "\<not> is_Var r"
      and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    have not_pair: "(l,r) \<notin> Rgt"
    proof
      assume strict: "(l,r) \<in> Rgt"
      have "(l \<cdot> \<sigma>,r \<cdot> \<sigma>) \<in> Rgt"
        by (rule subst.closedD[OF rp.subst_S strict])
      with not_strict show False unfolding s t by contradiction
    qed
    have "muterm_noncollapsing_rrstep (P - Rgt) s t"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def'
      using pair not_pair rhs s t by auto
    then show ?thesis unfolding st muterm_typed_pair_step_def by auto
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
    then obtain x l y \<sigma> where pair: "(l,Var y) \<in> P"
      and s: "s = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      and bridge: "(x,t) \<in> rrstep B"
      unfolding muterm_collapsing_rrstep_def by auto
    have not_pair: "(l,Var y) \<notin> Rgt"
    proof
      assume strict: "(l,Var y) \<in> Rgt"
      have inst: "(l \<cdot> \<sigma>,Var y \<cdot> \<sigma>) \<in> Rgt"
        by (rule subst.closedD[OF rp.subst_S strict])
      have sx: "(s,x) \<in> Rgt" unfolding s x using inst by simp
      from bridge obtain a b \<tau> where ab: "(a,b) \<in> B"
        and x': "x = a \<cdot> \<tau>" and t: "t = b \<cdot> \<tau>"
        unfolding rrstep_def' by auto
      from bridges ab have weak: "(a,b) \<in> Rge" by auto
      have xt: "(x,t) \<in> Rge" unfolding x' t
        by (rule subst.closedD[OF rp.subst_NS weak])
      from rp.compat_S_NS sx xt have "(s,t) \<in> Rgt" by auto
      with not_strict show False by contradiction
    qed
    have pair': "muterm_collapsing_rrstep (P - Rgt) s x"
      unfolding muterm_collapsing_rrstep_def
      using pair not_pair s x by auto
    show ?thesis unfolding st muterm_typed_pair_step_def
      using pair' bridge by auto
  qed
qed

lemma SN_rel_interpreted_redpair:
  fixes I :: "'a \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and simulation:
      "A\<^sup>* O B O A\<^sup>* \<subseteq>
        {(s,t). (I s,I t) \<in> Rgt \<union> Rge}"
    and residual:
      "(A\<^sup>* O B O A\<^sup>*) -
         {(s,t). (I s,I t) \<in> Rgt} \<subseteq>
       A\<^sup>* O C O A\<^sup>*"
    and fin: "SN_rel C A"
  shows "SN_rel B A"
proof (rule ccontr)
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  let ?PB = "A\<^sup>* O B O A\<^sup>*"
  let ?PC = "A\<^sup>* O C O A\<^sup>*"
  assume not_fin: "\<not> SN_rel B A"
  then obtain f where chain: "chain ?PB f"
    unfolding SN_rel_on_def SN_defs by auto
  let ?g = "I \<circ> f"
  have image_chain: "chain (Rge \<union> Rgt) ?g"
  proof
    fix i
    have src: "(f i,f (Suc i)) \<in> ?PB" by (rule chain[rule_format])
    from simulation src have
      "(I (f i),I (f (Suc i))) \<in> Rgt \<union> Rge" by auto
    then show "(?g i,?g (Suc i)) \<in> Rge \<union> Rgt"
      by (simp add: Un_commute)
  qed
  have sn0: "SN_on Rgt {?g 0}"
    using rp.SN unfolding SN_on_def by auto
  from non_strict_ending[OF image_chain rp.compat_NS_S sn0]
  obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?g k,?g (Suc k)) \<in> Rge - Rgt" by auto
  let ?h = "shift f j"
  have residual_chain: "chain ?PC ?h"
  proof
    fix k
    have src: "(f (k+j),f (Suc (k+j))) \<in> ?PB"
      by (rule chain[rule_format])
    have not_strict: "(I (f (k+j)),I (f (Suc (k+j)))) \<notin> Rgt"
      using tail[of "k+j"] by (simp add: comp_def)
    have diff: "(f (k+j),f (Suc (k+j))) \<in>
      ?PB - {(s,t). (I s,I t) \<in> Rgt}"
      using src not_strict by simp
    have member: "(f (k+j),f (Suc (k+j))) \<in> ?PC"
      by (rule residual[THEN subsetD, OF diff])
    show "(?h k,?h (Suc k)) \<in> ?PC" using member by simp
  qed
  from fin have "SN_on ?PC UNIV" unfolding SN_rel_on_def .
  moreover have "\<not> SN_on ?PC UNIV"
    by (rule not_SN_onI[OF _ residual_chain], simp)
  ultimately show False by contradiction
qed

lemma finite_muterm_min_typed_dpp_interpreted_redpair:
  fixes I :: "('f::{showl,compare_order},'v) term \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and simulation:
      "(csdp_step shp \<mu> R)\<^sup>* O
         muterm_min_typed_pair_step shp \<mu> R P S O
         (csdp_step shp \<mu> R)\<^sup>* \<subseteq>
       {(s,t). (I s,I t) \<in> Rgt \<union> Rge}"
    and residual:
      "((csdp_step shp \<mu> R)\<^sup>* O
          muterm_min_typed_pair_step shp \<mu> R P S O
          (csdp_step shp \<mu> R)\<^sup>*) -
         {(s,t). (I s,I t) \<in> Rgt} \<subseteq>
       (csdp_step shp \<mu> R)\<^sup>* O
         muterm_min_typed_pair_step shp \<mu> R Q S O
         (csdp_step shp \<mu> R)\<^sup>*"
    and fin: "finite_muterm_min_typed_dpp shp \<mu> R Q S"
  shows "finite_muterm_min_typed_dpp shp \<mu> R P S"
  unfolding finite_muterm_min_typed_dpp_def
  by (rule SN_rel_interpreted_redpair[
      OF redpair simulation residual
        fin[unfolded finite_muterm_min_typed_dpp_def]])

text \<open>
  Minimal-chain interpretation theorem.  In contrast to the relation-wide
  lemma above, rewrite simulation is required only between consecutive
  minimal pair events, where target normalization supplies exactly the
  induction premise used by MU-TERM's interpretation.
\<close>

lemma SN_rel_min_interpreted_redpair:
  fixes I :: "'a \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and target_SN: "\<And>s t. (s,t) \<in> B \<Longrightarrow> SN_on A {t}"
    and pair_order: "\<And>s t. SN_on A {s} \<Longrightarrow> (s,t) \<in> B \<Longrightarrow>
      (I s,I t) \<in> Rgt \<union> Rge"
    and pair_residual: "\<And>s t. SN_on A {s} \<Longrightarrow>
      (s,t) \<in> B \<Longrightarrow> (I s,I t) \<notin> Rgt \<Longrightarrow> (s,t) \<in> C"
    and steps_order: "\<And>s t. SN_on A {s} \<Longrightarrow>
      (s,t) \<in> A\<^sup>* \<Longrightarrow> (I s,I t) \<in> Rge"
    and fin: "SN_rel C A"
  shows "SN_rel B A"
proof (rule ccontr)
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  let ?PB = "A\<^sup>* O B O A\<^sup>*"
  let ?PC = "A\<^sup>* O C O A\<^sup>*"
  assume not_fin: "\<not> SN_rel B A"
  then obtain f where chain: "chain ?PB f"
    unfolding SN_rel_on_def SN_defs by auto
  have ex_mid: "\<forall>i. \<exists>a b. (f i,a) \<in> A\<^sup>* \<and>
      (a,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*"
  proof
    fix i
    from chain[rule_format, of i] obtain a b where
      pre: "(f i,a) \<in> A\<^sup>*" and pair: "(a,b) \<in> B"
      and post: "(b,f (Suc i)) \<in> A\<^sup>*" by auto
    show "\<exists>a b. (f i,a) \<in> A\<^sup>* \<and> (a,b) \<in> B \<and>
      (b,f (Suc i)) \<in> A\<^sup>*" using pre pair post by auto
  qed
  from choice[OF ex_mid] obtain a where choose_a:
      "\<forall>i. \<exists>b. (f i,a i) \<in> A\<^sup>* \<and>
        (a i,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*" by auto
  from choice[OF choose_a] obtain b where chosen:
      "\<forall>i. (f i,a i) \<in> A\<^sup>* \<and>
        (a i,b i) \<in> B \<and> (b i,f (Suc i)) \<in> A\<^sup>*" by auto
  from chosen have pre: "\<And>i. (f i,a i) \<in> A\<^sup>*"
    and pair: "\<And>i. (a i,b i) \<in> B"
    and post: "\<And>i. (b i,f (Suc i)) \<in> A\<^sup>*" by auto
  have between: "(b i,a (Suc i)) \<in> A\<^sup>*" for i
    by (rule rtrancl_trans[OF post[of i] pre[of "Suc i"]])
  have b_sn: "SN_on A {b i}" for i by (rule target_SN[OF pair])
  have a_sn: "SN_on A {a (Suc i)}" for i
  proof (rule ccontr)
    assume not_sn: "\<not> SN_on A {a (Suc i)}"
    from steps_notSN_on_source[OF between[of i] not_sn]
      b_sn[of i] show False by contradiction
  qed
  have weak: "(I (b i),I (a (Suc i))) \<in> Rge" for i
    by (rule steps_order[OF b_sn between])
  have pord: "(I (a (Suc i)),I (b (Suc i))) \<in> Rgt \<union> Rge" for i
    by (rule pair_order[OF a_sn pair])
  let ?x = "\<lambda>i. I (a (Suc i))"
  have xstep: "(?x i,?x (Suc i)) \<in> Rge \<union> Rgt" for i
  proof (cases "(I (a (Suc i)),I (b (Suc i))) \<in> Rgt")
    case True
    from rp.compat_S_NS True weak[of "Suc i"] have
      "(I (a (Suc i)),I (a (Suc (Suc i)))) \<in> Rgt" by auto
    then show ?thesis by simp
  next
    case False
    from False pord[of i] have first:
      "(I (a (Suc i)),I (b (Suc i))) \<in> Rge" by auto
    from rp.trans_NS_point[OF first weak[of "Suc i"]] show ?thesis by simp
  qed
  have xchain: "chain (Rge \<union> Rgt) ?x" using xstep by simp
  have sn0: "SN_on Rgt {?x 0}" using rp.SN unfolding SN_on_def by auto
  from non_strict_ending[OF xchain rp.compat_NS_S sn0]
  obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?x k,?x (Suc k)) \<in> Rge - Rgt" by auto
  have tail_pair: "(a (Suc (k+j)),b (Suc (k+j))) \<in> C" for k
  proof -
    have not_strict: "(I (a (Suc (k+j))),I (b (Suc (k+j)))) \<notin> Rgt"
    proof
      assume strict: "(I (a (Suc (k+j))),I (b (Suc (k+j)))) \<in> Rgt"
      have comp: "(I (a (Suc (k+j))),I (a (Suc (Suc (k+j))))) \<in> Rgt O Rge"
        by (rule relcompI[OF strict weak[of "Suc (k+j)"]])
      have "(?x (k+j),?x (Suc (k+j))) \<in> Rgt"
        by (rule rp.compat_S_NS[THEN subsetD, OF comp])
      moreover from tail[of "k+j"] have
        "(?x (k+j),?x (Suc (k+j))) \<notin> Rgt" by auto
      ultimately show False by contradiction
    qed
    show ?thesis by (rule pair_residual[OF a_sn pair not_strict])
  qed
  let ?h = "shift f (Suc j)"
  have residual_chain: "chain ?PC ?h"
  proof
    fix k
    have pre_k: "(f (Suc (k+j)),a (Suc (k+j))) \<in> A\<^sup>*" by (rule pre)
    have post_k: "(b (Suc (k+j)),f (Suc (Suc (k+j)))) \<in> A\<^sup>*" by (rule post)
    have member: "(f (Suc (k+j)),f (Suc (Suc (k+j)))) \<in> ?PC"
      using pre_k tail_pair[of k] post_k by auto
    show "(?h k,?h (Suc k)) \<in> ?PC" using member by simp
  qed
  from fin have "SN_on ?PC UNIV" unfolding SN_rel_on_def .
  moreover have "\<not> SN_on ?PC UNIV"
    by (rule not_SN_onI[OF _ residual_chain], simp)
  ultimately show False by contradiction
qed

lemma finite_muterm_min_typed_dpp_step_interpreted_redpair:
  fixes I :: "('f::{showl,compare_order},'v) term \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pair_order:
      "muterm_min_typed_pair_step shp \<mu> R P S \<subseteq>
        {(s,t). (I s,I t) \<in> Rgt \<union> Rge}"
    and pair_residual:
      "muterm_min_typed_pair_step shp \<mu> R P S -
         {(s,t). (I s,I t) \<in> Rgt} \<subseteq>
       muterm_min_typed_pair_step shp \<mu> R Q S"
    and steps_order: "\<And>s t.
      SN_on (csdp_step shp \<mu> R) {s} \<Longrightarrow>
      (s,t) \<in> (csdp_step shp \<mu> R)\<^sup>* \<Longrightarrow>
      (I s,I t) \<in> Rge"
    and fin: "finite_muterm_min_typed_dpp shp \<mu> R Q S"
  shows "finite_muterm_min_typed_dpp shp \<mu> R P S"
proof -
  have target: "\<And>s t.
    (s,t) \<in> muterm_min_typed_pair_step shp \<mu> R P S \<Longrightarrow>
    SN_on (csdp_step shp \<mu> R) {t}"
    unfolding muterm_min_typed_pair_step_def by auto
  show ?thesis unfolding finite_muterm_min_typed_dpp_def
  proof (rule SN_rel_min_interpreted_redpair[
      OF redpair target _ _ steps_order
        fin[unfolded finite_muterm_min_typed_dpp_def]])
    fix s t
    assume "SN_on (csdp_step shp \<mu> R) {s}"
      and pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> R P S"
    have "(s,t) \<in> {(s,t). (I s,I t) \<in> Rgt \<union> Rge}"
      by (rule pair_order[THEN subsetD, OF pair])
    then show "(I s,I t) \<in> Rgt \<union> Rge" by simp
  next
    fix s t
    assume "SN_on (csdp_step shp \<mu> R) {s}"
      and pair: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> R P S"
      and not_strict: "(I s,I t) \<notin> Rgt"
    have diff: "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> R P S -
      {(s,t). (I s,I t) \<in> Rgt}" using pair not_strict by simp
    show "(s,t) \<in> muterm_min_typed_pair_step shp \<mu> R Q S"
      by (rule pair_residual[THEN subsetD, OF diff])
  qed
qed

lemma muterm_typed_pair_step_target_marked:
  assumes pairs: "\<forall>(l,r)\<in>P. is_Var r \<or>
      (\<exists>f ts. r = Fun (Sharp f) ts)"
    and bridges: "\<forall>(l,r)\<in>B. \<exists>f ts. r = Fun (Sharp f) ts"
    and step: "(s,t) \<in> muterm_typed_pair_step P B"
  shows "\<exists>f ts. t = Fun (Sharp f) ts"
proof -
  from step have cases:
      "muterm_noncollapsing_rrstep P s t \<or>
       (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by auto
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P s t"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and nonvar: "\<not> is_Var r" and t: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    from pairs pair nonvar obtain f ts where r: "r = Fun (Sharp f) ts" by auto
    show ?thesis unfolding t r by auto
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
    then obtain x where bridge: "(x,t) \<in> rrstep B" by auto
    from bridge obtain l r \<sigma> where lr: "(l,r) \<in> B"
      and t: "t = r \<cdot> \<sigma>" unfolding rrstep_def' by auto
    from bridges lr obtain f ts where r: "r = Fun (Sharp f) ts" by auto
    show ?thesis unfolding t r by auto
  qed
qed

lemma muterm_min_typed_pair_step_target_marked:
  assumes pairs: "\<forall>(l,r)\<in>P. is_Var r \<or>
      (\<exists>f ts. r = Fun (Sharp f) ts)"
    and bridges: "\<forall>(l,r)\<in>B. \<exists>f ts. r = Fun (Sharp f) ts"
    and step: "(s,t) \<in> muterm_min_typed_pair_step Sharp \<mu> R P B"
  shows "\<exists>f ts. t = Fun (Sharp f) ts"
  by (rule muterm_typed_pair_step_target_marked[
      OF pairs bridges], use step in
      \<open>auto simp: muterm_min_typed_pair_step_def\<close>)

text \<open>
  The extended-basic MU-TERM processor needs one invariant that is stronger
  than ordinary minimal DP target normalization.  Its marked target denotes
  the minimal nonterminating active call selected by the MU-TERM extraction.
  Recording that fact makes the hidden substitution behind a collapsing pair
  available to the interpretation proof, without admitting arbitrary open
  typed macro steps.
\<close>

definition muterm_eb_min_typed_pair_step where
  "muterm_eb_min_typed_pair_step shp \<mu> R P B =
    muterm_min_typed_pair_step shp \<mu> R P B \<inter>
      {(s,t). \<exists>u. t = sharp_term shp u \<and>
        u \<in> mu_Tinf \<mu> (csstep \<mu> R)}"

definition finite_muterm_eb_min_typed_dpp where
  "finite_muterm_eb_min_typed_dpp shp \<mu> R P B \<longleftrightarrow>
    SN_rel (muterm_eb_min_typed_pair_step shp \<mu> R P B)
      (csdp_step shp \<mu> R)"

lemma exact_unhiding_bridge_exposes_active_target:
  fixes \<mu> :: "(('f::{showl,compare_order},'l::{showl,compare_order}) lab) muL"
  assumes exact: "B = set (muterm_exact_unhiding_rules_list Sharp \<mu> D Rs)"
    and bridge: "(x,sharp_term Sharp u) \<in> rrstep B"
  shows "x = u \<or> mu_supt (mu_of \<mu>) x u"
proof -
  from bridge obtain h v \<sigma> where hv: "(h,v) \<in> B"
    and x: "x = h \<cdot> \<sigma>"
    and target: "sharp_term Sharp u = v \<cdot> \<sigma>"
    unfolding rrstep_def' by blast
  from hv exact obtain t where v: "v = sharp_term Sharp t"
    and active: "muterm_active_defined_call_on (mu_of \<mu>) (set D) h t"
    unfolding muterm_exact_unhiding_rules_list_set by blast
  from active obtain p where p: "p \<in> mu_fun_poss (mu_of \<mu>) h"
    and at: "h |_ p = t" and root: "root t \<in> Some ` set D"
    unfolding muterm_active_defined_call_on_def by blast
  from root have t_fun: "is_Fun t" by (cases t, auto)
  have sharp_eq: "sharp_term Sharp u = sharp_term Sharp (t \<cdot> \<sigma>)"
    using target unfolding v
    by (simp add: sharp_term_subst_distr_2[OF t_fun])
  have target': "u = t \<cdot> \<sigma>"
    by (rule sharp_term_Sharp_inject[THEN iffD1, OF sharp_eq])
  have p_sub: "p \<in> mu_fun_poss (mu_of \<mu>) (h \<cdot> \<sigma>)"
    by (rule mu_fun_poss_subst_lift[OF p])
  have p_pos: "p \<in> mu_poss (mu_of \<mu>) (h \<cdot> \<sigma>)"
    by (rule mu_fun_poss_imp_mu_poss[OF p_sub])
  have at_sub: "(h \<cdot> \<sigma>) |_ p = t \<cdot> \<sigma>"
    using subt_at_subst[
      OF fun_poss_imp_poss[OF mu_fun_poss_imp_fun_poss[OF p]], of \<sigma>] at
    by simp
  show ?thesis
  proof (cases p)
    case Nil
    then show ?thesis using x target' at_sub by simp
  next
    case (Cons i q)
    have "mu_supt (mu_of \<mu>) (h \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
      unfolding mu_supt_def
      by (intro exI[of _ i] exI[of _ q], use p_pos at_sub Cons in auto)
    then show ?thesis unfolding x target' by blast
  qed
qed

lemma exact_unhiding_bridge_hidden_not_SN:
  fixes \<mu> :: "(('f::{showl,compare_order},'l::{showl,compare_order}) lab) muL"
  assumes wf: "wf_trs R"
    and exact: "B = set (muterm_exact_unhiding_rules_list Sharp \<mu> D Rs)"
    and bridge: "(x,sharp_term Sharp u) \<in> rrstep B"
    and uT: "u \<in> mu_Tinf (mu_of \<mu>) (csstep (mu_of \<mu>) R)"
  shows "\<not> SN_on (csstep (mu_of \<mu>) R) {x}"
proof
  assume xSN: "SN_on (csstep (mu_of \<mu>) R) {x}"
  from uT have u_not: "\<not> SN_on (csstep (mu_of \<mu>) R) {u}"
    unfolding mu_Tinf_def by auto
  from exact_unhiding_bridge_exposes_active_target[OF exact bridge]
  show False
  proof
    assume xu: "x = u"
    from xSN[unfolded xu] u_not show False by contradiction
  next
    assume xu: "mu_supt (mu_of \<mu>) x u"
    have unionSN: "SN_on
      (mu_supt_rel (mu_of \<mu>) \<union> csstep (mu_of \<mu>) R) {x}"
      by (rule SN_on_csstep_imp_SN_on_mu_supt_union[OF wf xSN])
    have step: "(x,u) \<in>
      mu_supt_rel (mu_of \<mu>) \<union> csstep (mu_of \<mu>) R"
      using xu unfolding mu_supt_rel_def by auto
    have u_union: "SN_on
      (mu_supt_rel (mu_of \<mu>) \<union> csstep (mu_of \<mu>) R) {u}"
      by (rule step_SN_on_target[OF unionSN step])
    have sub: "csstep (mu_of \<mu>) R \<subseteq>
      mu_supt_rel (mu_of \<mu>) \<union> csstep (mu_of \<mu>) R" by auto
    have "SN_on (csstep (mu_of \<mu>) R) {u}"
      by (rule SN_on_subset1[OF u_union sub])
    with u_not show False by contradiction
  qed
qed

lemma muterm_unhiding_relstep_eb_min_typed:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P B"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R B"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B u \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_eb_min_typed_pair_step Sharp \<mu> R P B"
proof -
  from muterm_unhiding_relstep_min_typed[
      OF wf fresh hp defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B u"
    and step: "(sharp_term Sharp t,sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step Sharp \<mu> R P B"
    by blast
  from hp_u have uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  from step obtain v where prefix:
      "(sharp_term Sharp t,v) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(v,sharp_term Sharp u) \<in>
      muterm_min_typed_pair_step Sharp \<mu> R P B" by auto
  have event': "(v,sharp_term Sharp u) \<in>
      muterm_eb_min_typed_pair_step Sharp \<mu> R P B"
    unfolding muterm_eb_min_typed_pair_step_def using event uT by auto
  show ?thesis using hp_u prefix event' by blast
qed

theorem finite_muterm_eb_min_typed_dpp_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P B"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R B"
    and fin: "finite_muterm_eb_min_typed_dpp Sharp \<mu> R P B"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where
    t0T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  let ?A = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_eb_min_typed_pair_step Sharp \<mu> R P B O
    (csdp_step Sharp \<mu> R)\<^sup>*"
  have step_ex: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (csstep \<mu> R) B t \<Longrightarrow>
      \<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B u \<and>
        (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
  proof -
    fix t
    assume hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B t"
    from muterm_unhiding_relstep_eb_min_typed[
        OF wf fresh hp defs cover preserving]
    obtain u where hp_u:
        "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B u"
      and step: "(sharp_term Sharp t,sharp_term Sharp u) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>* O
        muterm_eb_min_typed_pair_step Sharp \<mu> R P B" by blast
    show "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
      using hp_u step by auto
  qed
  have all_ex: "\<forall>t. \<exists>u.
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B t \<longrightarrow>
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
    using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
      "\<And>t. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B t \<Longrightarrow>
       has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B (nxt t) \<and>
       (sharp_term Sharp t,sharp_term Sharp (nxt t)) \<in> ?A" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have inv: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) B (ts n)"
    for n by (induct n, unfold ts_def, use hp0 nxt in auto)
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "(f n,f (Suc n)) \<in> ?A" for n
    using nxt[OF inv[of n]] unfolding f_def ts_def by auto
  from fin have sn: "SN ?A"
    unfolding finite_muterm_eb_min_typed_dpp_def SN_rel_on_def .
  moreover have "\<not> SN ?A" unfolding SN_defs using chain by blast
  ultimately show False by contradiction
qed

lemma finite_muterm_min_typed_imp_finite_eb:
  assumes fin: "finite_muterm_min_typed_dpp shp \<mu> R P B"
  shows "finite_muterm_eb_min_typed_dpp shp \<mu> R P B"
proof -
  have event_sub: "muterm_eb_min_typed_pair_step shp \<mu> R P B \<subseteq>
      muterm_min_typed_pair_step shp \<mu> R P B"
    unfolding muterm_eb_min_typed_pair_step_def by auto
  have rel_sub: "(csdp_step shp \<mu> R)\<^sup>* O
      muterm_eb_min_typed_pair_step shp \<mu> R P B O
      (csdp_step shp \<mu> R)\<^sup>* \<subseteq>
      (csdp_step shp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step shp \<mu> R P B O
      (csdp_step shp \<mu> R)\<^sup>*"
    by (meson relcomp_mono event_sub subset_refl)
  from fin have sn: "SN ((csdp_step shp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step shp \<mu> R P B O
      (csdp_step shp \<mu> R)\<^sup>*)"
    unfolding finite_muterm_min_typed_dpp_def SN_rel_on_def .
  have "SN ((csdp_step shp \<mu> R)\<^sup>* O
      muterm_eb_min_typed_pair_step shp \<mu> R P B O
      (csdp_step shp \<mu> R)\<^sup>*)"
    by (rule SN_subset[OF sn rel_sub])
  then show ?thesis
    unfolding finite_muterm_eb_min_typed_dpp_def SN_rel_on_def .
qed

definition muterm_extended_basic_ur_closed where
  "muterm_extended_basic_ur_closed R U \<mu> P B \<longleftrightarrow>
    U \<subseteq> R \<and>
    (\<forall>lr\<in>({dp \<in> P. is_Fun (snd dp)} \<union> B \<union> U).
      csr_u3_root_rules_closed R U (fst lr)
        (fun_poss (fst lr) - mu_fun_poss \<mu> (fst lr)) \<and>
      csr_u3_root_rules_closed R U (snd lr)
        (mu_fun_poss \<mu> (snd lr)))"

definition muterm_extended_basic_ur_closed_check where
  "muterm_extended_basic_ur_closed_check R U \<mu> P B =
    (list_all (\<lambda>lr. lr \<in> set R) U \<and>
     list_all (\<lambda>lr.
       csr_u3_inactive_root_rules_check R U \<mu> (fst lr) \<and>
       csr_rta08_active_root_rules_check R U \<mu> (snd lr))
       (muterm_extended_basic_seed_list P B U))"

lemma muterm_extended_basic_ur_closed_check_sound:
  assumes check: "muterm_extended_basic_ur_closed_check R U \<mu> P B"
  shows "muterm_extended_basic_ur_closed (set R) (set U) (mu_of \<mu>)
    (set P) (set B)"
proof -
  from check have subset: "set U \<subseteq> set R"
    and seed: "\<And>lr. lr \<in> set (muterm_extended_basic_seed_list P B U) \<Longrightarrow>
      csr_u3_inactive_root_rules_check R U \<mu> (fst lr) \<and>
      csr_rta08_active_root_rules_check R U \<mu> (snd lr)"
    unfolding muterm_extended_basic_ur_closed_check_def
    by (auto simp: list_all_iff)
  have closed: "\<forall>lr. lr \<in> {dp \<in> set P. is_Fun (snd dp)} \<union> set B \<union> set U \<longrightarrow>
      csr_u3_root_rules_closed (set R) (set U) (fst lr)
        (fun_poss (fst lr) - mu_fun_poss (mu_of \<mu>) (fst lr)) \<and>
      csr_u3_root_rules_closed (set R) (set U) (snd lr)
        (mu_fun_poss (mu_of \<mu>) (snd lr))"
  proof (intro allI)
    fix lr
    show "lr \<in> {dp \<in> set P. is_Fun (snd dp)} \<union> set B \<union> set U \<longrightarrow>
      csr_u3_root_rules_closed (set R) (set U) (fst lr)
        (fun_poss (fst lr) - mu_fun_poss (mu_of \<mu>) (fst lr)) \<and>
      csr_u3_root_rules_closed (set R) (set U) (snd lr)
        (mu_fun_poss (mu_of \<mu>) (snd lr))"
    proof
      assume lr: "lr \<in> {dp \<in> set P. is_Fun (snd dp)} \<union> set B \<union> set U"
      from seed[of lr] lr have lhs:
          "csr_u3_inactive_root_rules_check R U \<mu> (fst lr)"
        and rhs: "csr_rta08_active_root_rules_check R U \<mu> (snd lr)"
        by auto
      have inactive_eq:
          "fun_poss (fst lr) - mu_fun_poss (mu_of \<mu>) (fst lr) =
           {p \<in> fun_poss (fst lr). p \<notin> mu_fun_poss (mu_of \<mu>) (fst lr)}"
        by auto
      have lhs_closed: "csr_u3_root_rules_closed (set R) (set U) (fst lr)
          (fun_poss (fst lr) - mu_fun_poss (mu_of \<mu>) (fst lr))"
        unfolding inactive_eq
        by (rule csr_u3_inactive_root_rules_check_sound[OF lhs])
      have rhs_closed: "csr_u3_root_rules_closed (set R) (set U) (snd lr)
          (mu_fun_poss (mu_of \<mu>) (snd lr))"
        by (rule csr_rta08_active_root_rules_check_sound[OF rhs])
      show "csr_u3_root_rules_closed (set R) (set U) (fst lr)
          (fun_poss (fst lr) - mu_fun_poss (mu_of \<mu>) (fst lr)) \<and>
        csr_u3_root_rules_closed (set R) (set U) (snd lr)
          (mu_fun_poss (mu_of \<mu>) (snd lr))"
        using lhs_closed rhs_closed by blast
    qed
  qed
  show ?thesis unfolding muterm_extended_basic_ur_closed_def
  proof (intro conjI)
    show "set U \<subseteq> set R" by (rule subset)
    show "\<forall>lr\<in>{dp \<in> set P. is_Fun (snd dp)} \<union> set B \<union> set U.
      csr_u3_root_rules_closed (set R) (set U) (fst lr)
        (fun_poss (fst lr) - mu_fun_poss (mu_of \<mu>) (fst lr)) \<and>
      csr_u3_root_rules_closed (set R) (set U) (snd lr)
        (mu_fun_poss (mu_of \<mu>) (snd lr))"
      using closed by blast
  qed
qed

context muterm_i2_strong
begin

lemma i2_sharp_csdp_steps_redpair_weak:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<And>f n. \<mu> (shp f,n) = \<mu> (f,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and source: "s = Fun (shp f) ss"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
    and steps: "(s,t) \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
  shows "(i2 s,i2 t) \<in> Rge"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from i2_sharp_csdp_steps[
      OF fresh marked_inj marked_mu[of f "length ss"] source SN steps]
  have transformed:
    "(i2 s,i2 t) \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*" .
  have in_star: "(i2 s,i2 t) \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF transformed])
  show ?thesis using in_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
qed

lemma i2_noncollapsing_pair_redpair_order:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<And>f n. \<mu> (shp f,n) = \<mu> (f,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and pairs_in: "P \<subseteq> T"
    and pair_shape: "\<forall>(l,r)\<in>P.
      (\<exists>f ls. l = Fun (shp f) ls) \<and>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
    and target_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
    and pair_step: "muterm_noncollapsing_rrstep P s t"
  shows "(i2 s,i2 t) \<in> Rgt \<union> Rge"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from pair_step obtain l r \<sigma> where pair: "(l,r) \<in> P"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
  from pair_shape pair obtain f ls g rs where
    l: "l = Fun (shp f) ls" and r: "r = Fun (shp g) rs" by auto
  have source_form: "s = Fun (shp f) (map (\<lambda>u. u \<cdot> \<sigma>) ls)"
    unfolding s l by simp
  have source_marked:
    "\<mu> (shp f,length (map (\<lambda>u. u \<cdot> \<sigma>) ls)) =
      \<mu> (f,length (map (\<lambda>u. u \<cdot> \<sigma>) ls))"
    by (rule marked_mu)
  have source_cs_SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    unfolding source_form
    by (rule SN_sharp_csdp_imp_SN_csstep[
        OF fresh source_marked source_SN[unfolded source_form]])
  have target_form: "t = Fun (shp g) (map (\<lambda>u. u \<cdot> \<sigma>) rs)"
    unfolding t r by simp
  have target_marked:
    "\<mu> (shp g,length (map (\<lambda>u. u \<cdot> \<sigma>) rs)) =
      \<mu> (g,length (map (\<lambda>u. u \<cdot> \<sigma>) rs))"
    by (rule marked_mu)
  have target_cs_SN: "SN_on (csstep \<mu> (set Rs)) {t}"
    unfolding target_form
    by (rule SN_sharp_csdp_imp_SN_csstep[
        OF fresh target_marked target_SN[unfolded target_form]])
  let ?\<tau> = "i2_subst r \<sigma>"
  have adjust0: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in>
      (csstep \<mu> (ce_trs cn))\<^sup>*"
    by (rule i2_pair_adjust[OF pairs_in[THEN subsetD, OF pair]
          source_cs_SN[unfolded s]])
  have ce_sub: "csstep \<mu> (ce_trs cn) \<subseteq>
      csstep \<mu> (U \<union> ce_trs cn)"
    by (rule csstep_rules_mono, simp)
  have adjust1: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in>
      (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    by (rule rtrancl_mono[OF ce_sub, THEN subsetD, OF adjust0])
  have adjust_star: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF adjust1])
  have adjust: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge"
    using adjust_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
  have rhs: "i2 (r \<cdot> \<sigma>) = r \<cdot> ?\<tau>"
    by (rule i2_pair_rhs[OF pairs_in[THEN subsetD, OF pair]
          target_cs_SN[unfolded t]])
  from pairs_order pair have pair_ord: "(l,r) \<in> Rgt \<union> Rge" by auto
  show ?thesis
  proof (cases "(l,r) \<in> Rgt")
    case True
    have strict: "(l \<cdot> ?\<tau>,r \<cdot> ?\<tau>) \<in> Rgt"
      by (rule subst.closedD[OF rp.subst_S True])
    have comp: "(i2 (l \<cdot> \<sigma>),r \<cdot> ?\<tau>) \<in> Rge O Rgt"
      by (rule relcompI[OF adjust strict])
    have "(i2 (l \<cdot> \<sigma>),r \<cdot> ?\<tau>) \<in> Rgt"
      by (rule rp.compat_NS_S[THEN subsetD, OF comp])
    then show ?thesis unfolding s t rhs by simp
  next
    case False
    with pair_ord have weak_pair: "(l,r) \<in> Rge" by auto
    have weak_inst: "(l \<cdot> ?\<tau>,r \<cdot> ?\<tau>) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS weak_pair])
    from rp.trans_NS_point[OF adjust weak_inst]
    show ?thesis unfolding s t rhs by simp
  qed
qed

end

end
