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

lemma finite_muterm_eb_min_typed_dpp_step_interpreted_redpair:
  fixes I :: "('f::{showl,compare_order},'v) term \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pair_order: "\<And>s t.
      SN_on (csdp_step shp \<mu> R) {s} \<Longrightarrow>
      (s,t) \<in> muterm_eb_min_typed_pair_step shp \<mu> R P B \<Longrightarrow>
      (I s,I t) \<in> Rgt \<union> Rge"
    and pair_residual: "\<And>s t.
      SN_on (csdp_step shp \<mu> R) {s} \<Longrightarrow>
      (s,t) \<in> muterm_eb_min_typed_pair_step shp \<mu> R P B \<Longrightarrow>
      (I s,I t) \<notin> Rgt \<Longrightarrow>
      (s,t) \<in> muterm_eb_min_typed_pair_step shp \<mu> R Q B"
    and steps_order: "\<And>s t.
      SN_on (csdp_step shp \<mu> R) {s} \<Longrightarrow>
      (s,t) \<in> (csdp_step shp \<mu> R)\<^sup>* \<Longrightarrow>
      (I s,I t) \<in> Rge"
    and fin: "finite_muterm_eb_min_typed_dpp shp \<mu> R Q B"
  shows "finite_muterm_eb_min_typed_dpp shp \<mu> R P B"
proof -
  have target: "\<And>s t.
    (s,t) \<in> muterm_eb_min_typed_pair_step shp \<mu> R P B \<Longrightarrow>
    SN_on (csdp_step shp \<mu> R) {t}"
    unfolding muterm_eb_min_typed_pair_step_def
      muterm_min_typed_pair_step_def by auto
  show ?thesis unfolding finite_muterm_eb_min_typed_dpp_def
  proof (rule SN_rel_min_interpreted_redpair[
      OF redpair target _ _ steps_order
        fin[unfolded finite_muterm_eb_min_typed_dpp_def]])
    fix s t
    assume source: "SN_on (csdp_step shp \<mu> R) {s}"
      and pair: "(s,t) \<in> muterm_eb_min_typed_pair_step shp \<mu> R P B"
    show "(I s,I t) \<in> Rgt \<union> Rge"
      by (rule pair_order[OF source pair])
  next
    fix s t
    assume source: "SN_on (csdp_step shp \<mu> R) {s}"
      and pair: "(s,t) \<in> muterm_eb_min_typed_pair_step shp \<mu> R P B"
      and not_strict: "(I s,I t) \<notin> Rgt"
    show "(s,t) \<in> muterm_eb_min_typed_pair_step shp \<mu> R Q B"
      by (rule pair_residual[OF source pair not_strict])
  qed
qed

definition muterm_extended_basic_ur_closed where
  "muterm_extended_basic_ur_closed R U \<mu> P B \<longleftrightarrow>
    U \<subseteq> R \<and>
    (\<forall>lr\<in>({dp \<in> P. is_Fun (snd dp)} \<union> B \<union> U).
      csr_u3_root_rules_closed R U (snd lr)
        (mu_fun_poss \<mu> (snd lr)))"

definition muterm_extended_basic_ur_closed_check where
  "muterm_extended_basic_ur_closed_check R U \<mu> P B =
    (list_all (\<lambda>lr. lr \<in> set R) U \<and>
     list_all (\<lambda>lr.
       csr_rta08_active_root_rules_check R U \<mu> (snd lr))
       (muterm_extended_basic_seed_list P B U))"

lemma muterm_extended_basic_ur_closed_check_sound:
  assumes check: "muterm_extended_basic_ur_closed_check R U \<mu> P B"
  shows "muterm_extended_basic_ur_closed (set R) (set U) (mu_of \<mu>)
    (set P) (set B)"
proof -
  from check have subset: "set U \<subseteq> set R"
    and seed: "\<And>lr. lr \<in> set (muterm_extended_basic_seed_list P B U) \<Longrightarrow>
      csr_rta08_active_root_rules_check R U \<mu> (snd lr)"
    unfolding muterm_extended_basic_ur_closed_check_def
    by (auto simp: list_all_iff)
  have closed: "\<forall>lr. lr \<in> {dp \<in> set P. is_Fun (snd dp)} \<union> set B \<union> set U \<longrightarrow>
      csr_u3_root_rules_closed (set R) (set U) (snd lr)
        (mu_fun_poss (mu_of \<mu>) (snd lr))"
  proof (intro allI)
    fix lr
    show "lr \<in> {dp \<in> set P. is_Fun (snd dp)} \<union> set B \<union> set U \<longrightarrow>
      csr_u3_root_rules_closed (set R) (set U) (snd lr)
        (mu_fun_poss (mu_of \<mu>) (snd lr))"
    proof
      assume lr: "lr \<in> {dp \<in> set P. is_Fun (snd dp)} \<union> set B \<union> set U"
      from seed[of lr] lr have rhs:
          "csr_rta08_active_root_rules_check R U \<mu> (snd lr)"
        by auto
      have rhs_closed: "csr_u3_root_rules_closed (set R) (set U) (snd lr)
          (mu_fun_poss (mu_of \<mu>) (snd lr))"
        by (rule csr_rta08_active_root_rules_check_sound[OF rhs])
      show "csr_u3_root_rules_closed (set R) (set U) (snd lr)
          (mu_fun_poss (mu_of \<mu>) (snd lr))"
        by (rule rhs_closed)
    qed
  qed
  show ?thesis unfolding muterm_extended_basic_ur_closed_def
  proof (intro conjI)
    show "set U \<subseteq> set R" by (rule subset)
    show "\<forall>lr\<in>{dp \<in> set P. is_Fun (snd dp)} \<union> set B \<union> set U.
      csr_u3_root_rules_closed (set R) (set U) (snd lr)
        (mu_fun_poss (mu_of \<mu>) (snd lr))"
      using closed by blast
  qed
qed

text \<open>
  The side condition used by the extended-basic processor is deliberately
  weaker than @{const muterm_strongly_conservative}.  Definition 16 and
  Theorem 4 of the MU-TERM development require the non-collapsing pairs
  together with their usable rules to be left-linear and conservative with
  respect to the replacement map.  In particular, a variable may occur both
  below an active and below an inactive position; excluding that case is the
  stronger, chain-independent interpretation used by the legacy processor
  and loses Ex1_GM03.
\<close>

definition muterm_extended_basic_noncollapsing where
  "muterm_extended_basic_noncollapsing P \<longleftrightarrow>
    (\<forall>(l,r)\<in>P. is_Fun r)"

definition muterm_extended_basic_side_conditions where
  "muterm_extended_basic_side_conditions \<mu> P U \<longleftrightarrow>
    muterm_extended_basic_noncollapsing P \<and>
    left_linear_trs (P \<union> U) \<and>
    rhs_mu_vars_condition \<mu> (P \<union> U) \<and>
    (\<forall>(l,r)\<in>P \<union> U.
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {})"

definition muterm_extended_basic_side_conditions_check where
  "muterm_extended_basic_side_conditions_check \<mu> P U = do {
    check (list_all (is_Fun \<circ> snd) P)
      (showsl_lit (STR ''extended-basic processor requires non-collapsing pairs''));
    check_left_linear_trs (P @ U);
    check (rhs_mu_vars_condition_list \<mu> (P @ U))
      (showsl_lit (STR ''extended-basic conservativity condition failed''));
    check (list_all (\<lambda>(l,r).
      set (mu_vars_term_list \<mu> l) \<inter>
        set (non_mu_vars_term_list \<mu> l) = {}) (P @ U))
      (showsl_lit (STR ''extended-basic left-hand-side activity partition failed''))
  }"


lemma muterm_extended_basic_side_conditions_check_sound:
  assumes ok: "isOK
    (muterm_extended_basic_side_conditions_check \<mu> P U)"
  shows "muterm_extended_basic_side_conditions (mu_of \<mu>) (set P) (set U)"
proof -
  from ok have nc: "\<forall>lr\<in>set P. is_Fun (snd lr)"
    and ll: "left_linear_trs (set (P @ U))"
    and cons_check: "rhs_mu_vars_condition_list \<mu> (P @ U)"
    and lhs_check: "list_all (\<lambda>(l,r).
      set (mu_vars_term_list \<mu> l) \<inter>
        set (non_mu_vars_term_list \<mu> l) = {}) (P @ U)"
    unfolding muterm_extended_basic_side_conditions_check_def
    by (auto simp: list_all_iff)
  have cons: "rhs_mu_vars_condition (mu_of \<mu>) (set (P @ U))"
    by (rule rhs_mu_vars_condition_list_sound[OF cons_check])
  have lhs': "\<And>l r. (l,r) \<in> set P \<union> set U \<Longrightarrow>
      mu_vars_term (mu_of \<mu>) l \<inter>
        non_mu_vars_term (mu_of \<mu>) l = {}"
    using lhs_check
    by (auto simp: list_all_iff split: prod.splits)
  show ?thesis
    unfolding muterm_extended_basic_side_conditions_def
      muterm_extended_basic_noncollapsing_def
  proof (intro conjI)
    show "\<forall>(l,r)\<in>set P. is_Fun r"
      using nc by (auto split: prod.splits)
    show "left_linear_trs (set P \<union> set U)"
      using ll by simp
    show "rhs_mu_vars_condition (mu_of \<mu>) (set P \<union> set U)"
      using cons by simp
    show "\<forall>(l,r)\<in>set P \<union> set U.
        mu_vars_term (mu_of \<mu>) l \<inter>
          non_mu_vars_term (mu_of \<mu>) l = {}"
      using lhs' by (auto split: prod.splits)
  qed
qed

context muterm_i2
begin

text \<open>
  The chain-parametric seam needed by the extended-basic processor.  The
  substitution is selected from the (linear) pair left-hand side.  At an
  inactive right-hand-side occurrence an interpreted substitution value may
  be projected back with C-epsilon.  This is an ordinary context step, not a
  context-sensitive step; consequently the eventual processor requires a
  standard (hence fully monotone) reduction pair, as CPF polynomial and matrix
  orders provide.
\<close>

lemma i2_projects_self_total:
  "(i2 t,t) \<in> (rstep (ce_trs cn))\<^sup>*"
proof (cases "SN_on (csstep \<mu> (set Rs)) {t}")
  case True
  from i2_projects_self[OF True]
  show ?thesis
    by (rule rtrancl_mono[OF csstep_subset_rstep, THEN subsetD])
next
  case False
  have "i2 t = t"
  proof (cases t)
    case (Var x)
    then show ?thesis by simp
  next
    case (Fun f ts)
    then show ?thesis using False by (simp add: i2_Fun)
  qed
  then show ?thesis by simp
qed

lemma i2_lhs_subst_projects_value:
  assumes x: "x \<in> vars_term l"
  shows "(i2_subst l \<sigma> x, \<sigma> x) \<in> (rstep (ce_trs cn))\<^sup>*"
proof (cases "x \<in> mu_vars_term \<mu> l")
  case False
  then show ?thesis unfolding i2_subst_def by simp
next
  case True
  from i2_projects_self_total[of "\<sigma> x"]
  show ?thesis unfolding i2_subst_def using True by simp
qed

lemma i2_lhs_subst_to_bracket_rsteps:
  assumes active_sub: "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
  shows "(r \<cdot> i2_subst l \<sigma>, i2_bracket r \<sigma>)
    \<in> (rstep (ce_trs cn))\<^sup>*"
  using active_sub
proof (induct r)
  case (Var x)
  have active: "x \<in> mu_vars_term \<mu> (Var x)"
    unfolding mu_vars_term_def by simp
  from Var.prems active have "x \<in> mu_vars_term \<mu> l" by blast
  then show ?case unfolding i2_subst_def by simp
next
  case (Fun f ts)
  let ?ss = "map (\<lambda>t. t \<cdot> i2_subst l \<sigma>) ts"
  let ?us = "args (i2_bracket (Fun f ts) \<sigma>)"
  have len: "length ?ss = length ?us" by simp
  have args: "\<And>i. i < length ?ss \<Longrightarrow>
    (?ss ! i, ?us ! i) \<in> (rstep (ce_trs cn))\<^sup>*"
  proof -
    fix i
    assume iss: "i < length ?ss"
    then have i: "i < length ts" by simp
    show "(?ss ! i, ?us ! i) \<in> (rstep (ce_trs cn))\<^sup>*"
    proof (cases "i \<in> \<mu> (f,length ts)")
      case True
      have child_sub: "mu_vars_term \<mu> (ts ! i) \<subseteq>
          mu_vars_term \<mu> l"
      proof
        fix x
        assume x: "x \<in> mu_vars_term \<mu> (ts ! i)"
        have "x \<in> mu_vars_term \<mu> (Fun f ts)"
          by (rule mu_vars_term_active_argI[OF i True x])
        with Fun.prems show "x \<in> mu_vars_term \<mu> l" by blast
      qed
      from Fun.hyps[OF nth_mem[OF i] child_sub]
      show ?thesis using i True
        by (simp add: i2_bracket_Fun_nth)
    next
      case False
      have point: "\<And>x. x \<in> vars_term (ts ! i) \<Longrightarrow>
        (i2_subst l \<sigma> x,\<sigma> x) \<in> (rstep (ce_trs cn))\<^sup>*"
      proof -
        fix x
        assume x: "x \<in> vars_term (ts ! i)"
        have xl: "x \<in> vars_term l \<or> x \<notin> vars_term l" by blast
        show "(i2_subst l \<sigma> x,\<sigma> x) \<in>
          (rstep (ce_trs cn))\<^sup>*"
        proof (cases "x \<in> vars_term l")
          case True
          show ?thesis by (rule i2_lhs_subst_projects_value[OF True])
        next
          case False
          then have "x \<notin> mu_vars_term \<mu> l"
            by (meson mu_vars_term_imp_vars_term)
          then show ?thesis unfolding i2_subst_def by simp
        qed
      qed
      have step: "((ts ! i) \<cdot> i2_subst l \<sigma>,
          (ts ! i) \<cdot> \<sigma>) \<in> (rstep (ce_trs cn))\<^sup>*"
        by (rule term_subst_rsteps[OF point])
      show ?thesis using i False step
        by (simp add: i2_bracket_Fun_nth)
    qed
  qed
  have "(Fun f ?ss,Fun f ?us) \<in> (rstep (ce_trs cn))\<^sup>*"
  proof (rule args_rsteps_imp_rsteps)
    show "length ?ss = length ?us" by (rule len)
    show "\<forall>i<length ?ss.
        (?ss ! i, ?us ! i) \<in> (rstep (ce_trs cn))\<^sup>*"
      using args by simp
  qed
  then show ?case by simp
qed

end

locale muterm_i2_extended_basic =
  muterm_i2 Rs \<mu> \<Delta> cn
  for Rs :: "('f::{showl,compare_order},'v) rules"
    and \<mu> :: "('f \<times> nat) \<Rightarrow> nat set"
    and \<Delta> :: "('f \<times> nat) set"
    and cn :: "'f \<times> nat" +
  fixes U T :: "('f,'v) trs"
  assumes delta: "\<Delta> = csr_u3_delta (set Rs) U"
    and closed_rhs: "\<And>l r. (l,r) \<in> T \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
    and conservative: "rhs_mu_vars_condition \<mu> T"
    and lhs_partition: "\<And>l r. (l,r) \<in> T \<Longrightarrow>
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and usable_in: "U \<subseteq> T"
    and lhs_T: "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l"
begin

lemma eb_active_variables:
  assumes lr: "(l,r) \<in> T"
  shows "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
  using conservative lr unfolding rhs_mu_vars_condition_def by blast

lemma i2_root_csstep_extended_basic:
  assumes root_delta: "root s \<in> Some ` \<Delta>"
    and SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and step: "(s,t) \<in> csrstep \<mu> (set Rs)"
  shows "(i2 s,i2 t) \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> set Rs"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain f ls where l: "l = Fun f ls"
    unfolding wf_trs_def by (cases l, auto)
  have root_l: "root l = Some (f,length ls)" unfolding l by simp
  have root_s: "root s = Some (f,length ls)" unfolding s l by simp
  from root_delta root_s have in_delta: "(f,length ls) \<in> \<Delta>" by auto
  have in_delta': "(f,length ls) \<in> csr_u3_delta (set Rs) U"
    using in_delta unfolding delta .
  have lrU: "(l,r) \<in> U"
    using in_delta' lr root_l unfolding csr_u3_delta_def by auto
  have lrT: "(l,r) \<in> T" using usable_in lrU by blast
  let ?sl = "i2_subst l \<sigma>"
  from i2_projects_to_bracket[OF SN[unfolded s]]
  have lhs_project0: "(i2 (l \<cdot> \<sigma>),i2_bracket l \<sigma>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
  have lhs_bracket: "i2_bracket l \<sigma> = l \<cdot> ?sl"
    by (rule i2_bracket_as_subst[OF lhs_partition[OF lrT]])
  have lhs_project_cs: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?sl)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    using lhs_project0 unfolding lhs_bracket .
  have cs_ce_r: "csstep \<mu> (ce_trs cn) \<subseteq>
      rstep (U \<union> ce_trs cn)"
    by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
  have lhs_project: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?sl)
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    by (rule rtrancl_mono[OF cs_ce_r, THEN subsetD, OF lhs_project_cs])
  have root_step: "(l \<cdot> ?sl,r \<cdot> ?sl)
      \<in> rstep (U \<union> ce_trs cn)"
  proof -
    have "(l \<cdot> ?sl,r \<cdot> ?sl) \<in> rrstep (U \<union> ce_trs cn)"
      by (rule rrstepI[where \<sigma> = ?sl], use lrU in auto)
    then show ?thesis by (simp add: rstep_iff_rrstep_or_nrrstep)
  qed
  have cs: "(s,t) \<in> csstep \<mu> (set Rs)"
    using step unfolding csstep_root_nonroot by auto
  have rhs_SN: "SN_on (csstep \<mu> (set Rs)) {r \<cdot> \<sigma>}"
    using step_SN_on_target[OF SN cs] unfolding t .
  have rhs_local: "(r \<cdot> ?sl,i2_bracket r \<sigma>)
      \<in> (rstep (ce_trs cn))\<^sup>*"
    by (rule i2_lhs_subst_to_bracket_rsteps[
      OF eb_active_variables[OF lrT]])
  have rhs_local': "(r \<cdot> ?sl,i2_bracket r \<sigma>)
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  proof -
    have rules_sub: "ce_trs cn \<subseteq> U \<union> ce_trs cn" by simp
    have steps_sub: "(rstep (ce_trs cn))\<^sup>* \<subseteq>
        (rstep (U \<union> ce_trs cn))\<^sup>*"
      by (rule rtrancl_mono, rule rstep_mono[OF rules_sub])
    show ?thesis by (rule steps_sub[THEN subsetD, OF rhs_local])
  qed
  have rhs_roots: "\<And>p. p \<in> mu_fun_poss \<mu> r \<Longrightarrow>
      root (r |_ p) \<in> Some ` \<Delta>"
  proof -
    fix p
    assume p: "p \<in> mu_fun_poss \<mu> r"
    from mu_fun_poss_imp_fun_poss[OF p] obtain g us where
      at: "r |_ p = Fun g us" using fun_poss_fun_conv by blast
    have root: "root (r |_ p) = Some (g,length us)" unfolding at by simp
    have "(g,length us) \<in> csr_u3_delta (set Rs) U"
      by (rule csr_u3_root_rules_closed_delta[
        OF closed_rhs[OF lrT] p root])
    then show "root (r |_ p) \<in> Some ` \<Delta>"
      unfolding delta root by blast
  qed
  have rhs_I: "i2 (r \<cdot> \<sigma>) = i2_bracket r \<sigma>"
    by (rule i2_equals_bracket[OF rhs_SN rhs_roots])
  have before: "(i2 (l \<cdot> \<sigma>),r \<cdot> ?sl)
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF lhs_project root_step])
  have total: "(i2 (l \<cdot> \<sigma>),i2_bracket r \<sigma>)
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    by (rule rtrancl_trans[OF before rhs_local'])
  show ?thesis unfolding s t rhs_I by (rule total)
qed

lemma i2_csstep_extended_basic:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and step: "(s,t) \<in> csstep \<mu> (set Rs)"
  shows "(i2 s,i2 t) \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  using SN step
proof (induct s arbitrary: t)
  case (Var x)
  from csstep_Var_empty_wf[OF wf, of x t \<mu>] Var.prems(2)
  show ?case by contradiction
next
  case (Fun f ss)
  let ?A = "rstep (U \<union> ce_trs cn)"
  show ?case
  proof (cases "(f,length ss) \<in> \<Delta>")
    case False
    from csrewrite_complete[OF wf Fun.prems(2)]
    have member: "i2 t \<in> set
      (Fun f (i2_args f ss) # map i2 (csrewrite \<mu> Rs (Fun f ss)))"
      by simp
    from ce_trs_sound_csstep[OF member, where \<mu>=\<mu>]
    have project: "(comb cn
      (Fun f (i2_args f ss) # map i2 (csrewrite \<mu> Rs (Fun f ss))),i2 t)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>+" .
    have source_I: "i2 (Fun f ss) = comb cn
      (Fun f (i2_args f ss) # map i2 (csrewrite \<mu> Rs (Fun f ss)))"
      apply (subst i2_Fun)
      using False Fun.prems(1) apply simp
      done
    have sub: "csstep \<mu> (ce_trs cn) \<subseteq> ?A"
      by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
    have "(i2 (Fun f ss),i2 t) \<in> ?A\<^sup>+"
      unfolding source_I by (rule trancl_mono[OF project sub])
    then show ?thesis by (rule trancl_into_rtrancl)
  next
    case True
    from Fun.prems(2) have cases:
      "(Fun f ss,t) \<in> csrstep \<mu> (set Rs) \<or>
       (Fun f ss,t) \<in> csnrstep \<mu> (set Rs)"
      unfolding csstep_root_nonroot by auto
    from cases show ?thesis
    proof
      assume root: "(Fun f ss,t) \<in> csrstep \<mu> (set Rs)"
      have root_delta: "root (Fun f ss) \<in> Some ` \<Delta>"
        using True by simp
      show ?thesis by (rule i2_root_csstep_extended_basic[
        OF root_delta Fun.prems(1) root])
    next
      assume nonroot: "(Fun f ss,t) \<in> csnrstep \<mu> (set Rs)"
      from nonroot obtain i ts where i: "i < length ss"
        and active: "i \<in> \<mu> (f,length ss)"
        and t: "t = Fun f ts" and len: "length ts = length ss"
        and substep: "(ss ! i,ts ! i) \<in> csstep \<mu> (set Rs)"
        and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
          ts ! j = ss ! j"
        by (elim csnrstep_FunE, blast)
      have empty: "[] \<in> mu_poss \<mu> (ss ! i)"
        by (cases "ss ! i") simp_all
      have pos: "i # [] \<in> mu_poss \<mu> (Fun f ss)"
        using i active empty by auto
      from SN_on_mu_pos[OF wf pos Fun.prems(1)]
      have sub_SN: "SN_on (csstep \<mu> (set Rs)) {ss ! i}"
        using i by simp
      from Fun.hyps[OF nth_mem[OF i], of "ts ! i", OF sub_SN substep]
      have sub_I: "(i2 (ss ! i),i2 (ts ! i)) \<in> ?A\<^sup>*" .
      have ts_update: "ts = ss[i := ts ! i]"
      proof (rule nth_equalityI)
        show "length ts = length (ss[i := ts ! i])" using len by simp
        fix j
        assume j: "j < length ts"
        show "ts ! j = (ss[i := ts ! i]) ! j"
        proof (cases "j=i")
          case True
          with i show ?thesis by simp
        next
          case False
          from j len have jss: "j < length ss" by simp
          from same[OF jss False] False i show ?thesis by simp
        qed
      qed
      have args_update: "i2_args f ts =
          (i2_args f ss)[i := i2 (ts ! i)]"
      proof (rule nth_equalityI)
        show "length (i2_args f ts) =
          length ((i2_args f ss)[i := i2 (ts ! i)])" using len by simp
        fix j
        assume j: "j < length (i2_args f ts)"
        then have jts: "j < length ts" by simp
        then have jss: "j < length ss" using len by simp
        show "i2_args f ts ! j =
          (i2_args f ss)[i := i2 (ts ! i)] ! j"
        proof (cases "j=i")
          case True
          then show ?thesis using i jts active len
            by (simp add: i2_args_nth)
        next
          case False
          have same_j: "ts ! j = ss ! j" by (rule same[OF jss False])
          show ?thesis using jts jss False len same_j
            by (simp add: i2_args_nth nth_list_update)
        qed
      qed
      have whole: "(Fun f (i2_args f ss),
          Fun f ((i2_args f ss)[i := i2 (ts ! i)])) \<in> ?A\<^sup>*"
      proof (rule args_rsteps_imp_rsteps)
        show "length (i2_args f ss) =
            length ((i2_args f ss)[i := i2 (ts ! i)])" by simp
        show "\<forall>j<length (i2_args f ss).
            (i2_args f ss ! j,
              (i2_args f ss)[i := i2 (ts ! i)] ! j) \<in> ?A\<^sup>*"
        proof (intro allI impI)
          fix j
          assume j: "j < length (i2_args f ss)"
          show "(i2_args f ss ! j,
              (i2_args f ss)[i := i2 (ts ! i)] ! j) \<in> ?A\<^sup>*"
          proof (cases "j=i")
            case True
            have source_nth: "i2_args f ss ! i = i2 (ss ! i)"
              using i active by (simp add: i2_args_nth)
            from True i source_nth sub_I show ?thesis by simp
          next
            case False
            with j show ?thesis by simp
          qed
        qed
      qed
      have target_SN: "SN_on (csstep \<mu> (set Rs)) {t}"
        by (rule step_SN_on_target[OF Fun.prems(1) Fun.prems(2)])
      have target_delta: "(f,length ts) \<in> \<Delta>" using True len by simp
      have source_I: "i2 (Fun f ss) = Fun f (i2_args f ss)"
        apply (subst i2_Fun)
        using True Fun.prems(1) apply simp
        done
      have target_I: "i2 t = Fun f (i2_args f ts)"
        unfolding t
        apply (subst i2_Fun)
        using target_delta target_SN t apply simp
        done
      show ?thesis unfolding source_I target_I args_update by (rule whole)
    qed
  qed
qed

lemma i2_cssteps_extended_basic:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and steps: "(s,t) \<in> (csstep \<mu> (set Rs))\<^sup>*"
  shows "(i2 s,i2 t) \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  using steps SN
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have y_SN: "SN_on (csstep \<mu> (set Rs)) {y}"
  proof (rule ccontr)
    assume "\<not> SN_on (csstep \<mu> (set Rs)) {y}"
    from steps_notSN_on_source[OF step.hyps(1) this]
      step.prems show False by contradiction
  qed
  have prefix: "(i2 s,i2 y) \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    by (rule step.hyps(3)[OF step.prems])
  have last: "(i2 y,i2 z) \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    by (rule i2_csstep_extended_basic[OF y_SN step.hyps(2)])
  show ?case by (rule rtrancl_trans[OF prefix last])
qed

lemma i2_sharp_csdp_step_extended_basic:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {Fun (shp f) ss}"
    and step: "(Fun (shp f) ss,t) \<in> csdp_step shp \<mu> (set Rs)"
  shows "(i2 (Fun (shp f) ss),i2 t)
    \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
proof -
  have step': "(sharp_term shp (Fun f ss),t)
      \<in> csdp_step shp \<mu> (set Rs)" using step by simp
  from sharp_csdp_step_imp_csnrstep[OF wf fresh marked_inj step']
  obtain u where t0: "t = sharp_term shp u"
    and nonroot: "(Fun f ss,u) \<in> csnrstep \<mu> (set Rs)" by blast
  from nonroot obtain i us where i: "i < length ss"
    and active: "i \<in> \<mu> (f,length ss)"
    and u: "u = Fun f us" and len: "length us = length ss"
    and substep: "(ss ! i,us ! i) \<in> csstep \<mu> (set Rs)"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      us ! j = ss ! j"
    by (elim csnrstep_FunE, blast)
  have t: "t = Fun (shp f) us" using t0 u by simp
  from SN_sharp_csdp_imp_SN_active_arg[OF i active SN]
  have sub_SN: "SN_on (csstep \<mu> (set Rs)) {ss ! i}" .
  from i2_csstep_extended_basic[OF sub_SN substep]
  have sub_I: "(i2 (ss ! i),i2 (us ! i))
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*" .
  have sharp_delta: "(shp f,length ss) \<in> \<Delta>"
  proof -
    have sharp_delta': "(shp f,length ss) \<in> csr_u3_delta (set Rs) U"
    proof (unfold csr_u3_delta_def, intro CollectI ballI impI)
      fix lr
      assume mem: "lr \<in> set Rs"
        and root: "root (fst lr) = Some (shp f,length ss)"
      from mem root have "defined (set Rs) (shp f,length ss)"
        unfolding defined_def
        by (intro exI[of _ "fst lr"] exI[of _ "snd lr"], simp)
      with fresh[of f "length ss"] show "lr \<in> U" by contradiction
    qed
    show ?thesis using sharp_delta' unfolding delta .
  qed
  have target_delta: "(shp f,length us) \<in> \<Delta>" using sharp_delta len by simp
  have source_cs_SN: "SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
  proof (rule ccontr)
    assume notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
    have undef: "\<not> defined (set Rs) (shp f,length ss)" by (rule fresh)
    from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf undef notSN]
    obtain j where j: "j < length ss"
      and active_j: "j \<in> \<mu> (shp f,length ss)"
      and notSN_j: "\<not> SN_on (csstep \<mu> (set Rs)) {ss ! j}" by blast
    have active_orig: "j \<in> \<mu> (f,length ss)" using active_j marked_mu by simp
    from SN_sharp_csdp_imp_SN_active_arg[OF j active_orig SN]
      notSN_j show False by contradiction
  qed
  have target_dp_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
    by (rule step_SN_on_target[OF SN step])
  have target_cs_SN: "SN_on (csstep \<mu> (set Rs)) {Fun (shp f) us}"
  proof (rule ccontr)
    assume notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun (shp f) us}"
    have undef: "\<not> defined (set Rs) (shp f,length us)" by (rule fresh)
    from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf undef notSN]
    obtain j where j: "j < length us"
      and active_j: "j \<in> \<mu> (shp f,length us)"
      and notSN_j: "\<not> SN_on (csstep \<mu> (set Rs)) {us ! j}" by blast
    have marked_mu_us: "\<mu> (shp f,length us) = \<mu> (f,length us)"
      using marked_mu len by simp
    have active_orig: "j \<in> \<mu> (f,length us)" using active_j marked_mu_us by simp
    have target_dp_SN': "SN_on (csdp_step shp \<mu> (set Rs))
        {Fun (shp f) us}" using target_dp_SN unfolding t .
    from SN_sharp_csdp_imp_SN_active_arg[OF j active_orig target_dp_SN']
      notSN_j show False by contradiction
  qed
  have us_update: "us = ss[i := us ! i]"
  proof (rule nth_equalityI)
    show "length us = length (ss[i := us ! i])" using len by simp
    fix j
    assume j: "j < length us"
    show "us ! j = (ss[i := us ! i]) ! j"
    proof (cases "j=i")
      case True
      with i show ?thesis by simp
    next
      case False
      from j len have jss: "j < length ss" by simp
      from same[OF jss False] False i show ?thesis by simp
    qed
  qed
  have marked_active: "i \<in> \<mu> (shp f,length (i2_args (shp f) ss))"
    using active marked_mu by auto
  have source_nth: "i2_args (shp f) ss ! i = i2 (ss ! i)"
    using i marked_active by (simp add: i2_args_nth)
  have whole: "(Fun (shp f) (i2_args (shp f) ss),
      Fun (shp f) ((i2_args (shp f) ss)[i := i2 (us ! i)]))
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
  proof (rule args_rsteps_imp_rsteps)
    show "length (i2_args (shp f) ss) =
        length ((i2_args (shp f) ss)[i := i2 (us ! i)])"
      by simp
    show "\<forall>j<length (i2_args (shp f) ss).
        (i2_args (shp f) ss ! j,
          (i2_args (shp f) ss)[i := i2 (us ! i)] ! j)
        \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    proof (intro allI impI)
      fix j
      assume j: "j < length (i2_args (shp f) ss)"
      show "(i2_args (shp f) ss ! j,
          (i2_args (shp f) ss)[i := i2 (us ! i)] ! j)
        \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
      proof (cases "j=i")
        case True
        with i source_nth sub_I show ?thesis by simp
      next
        case False
        with j show ?thesis by simp
      qed
    qed
  qed
  have args_update: "i2_args (shp f) us =
      (i2_args (shp f) ss)[i := i2 (us ! i)]"
  proof (rule nth_equalityI)
    show "length (i2_args (shp f) us) =
      length ((i2_args (shp f) ss)[i := i2 (us ! i)])" using len by simp
    fix j
    assume j: "j < length (i2_args (shp f) us)"
    then have jus: "j < length us" by simp
    then have jss: "j < length ss" using len by simp
    show "i2_args (shp f) us ! j =
      (i2_args (shp f) ss)[i := i2 (us ! i)] ! j"
    proof (cases "j=i")
      case True
      then show ?thesis using i jus marked_active len
        by (simp add: i2_args_nth)
    next
      case False
      have same_j: "us ! j = ss ! j" by (rule same[OF jss False])
      show ?thesis using jus jss False len same_j
        by (simp add: i2_args_nth nth_list_update)
    qed
  qed
  have source_I: "i2 (Fun (shp f) ss) = Fun (shp f) (i2_args (shp f) ss)"
    apply (subst i2_Fun)
    using sharp_delta source_cs_SN apply simp
    done
  have target_I: "i2 t = Fun (shp f) (i2_args (shp f) us)"
    unfolding t
    apply (subst i2_Fun)
    using target_delta target_cs_SN apply simp
    done
  show ?thesis unfolding source_I target_I args_update by (rule whole)
qed

lemma i2_sharp_csdp_steps_extended_basic:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and source: "s = Fun (shp f) ss"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
    and steps: "(s,t) \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
  shows "(i2 s,i2 t) \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
proof -
  have combined: "(i2 s,i2 t) \<in>
      (rstep (U \<union> ce_trs cn))\<^sup>* \<and>
      SN_on (csdp_step shp \<mu> (set Rs)) {t} \<and>
      (\<exists>us. t = Fun (shp f) us \<and> length us = length ss)"
    using steps SN source
  proof (induct rule: rtrancl_induct)
    case base
    then show ?case by auto
  next
    case (step y z)
    from step.hyps(3)[OF step.prems(1) step.prems(2)]
    have prefix: "(i2 s,i2 y) \<in>
        (rstep (U \<union> ce_trs cn))\<^sup>*"
      and y_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {y}"
      and y_shape: "\<exists>us. y = Fun (shp f) us \<and> length us = length ss"
      by blast+
    from y_shape obtain us where y: "y = Fun (shp f) us"
      and us_len: "length us = length ss" by blast
    have one: "(i2 y,i2 z) \<in>
        (rstep (U \<union> ce_trs cn))\<^sup>*"
      unfolding y
      apply (rule i2_sharp_csdp_step_extended_basic[
        where shp=shp and f=f and ss=us and t=z])
          apply (rule fresh)
         apply (rule marked_inj)
        using marked_mu us_len apply simp
       using y_SN y apply simp
      using step.hyps(2) y apply simp
      done
    have z_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {z}"
      by (rule step_SN_on_target[OF y_SN step.hyps(2)])
    have z_shape: "\<exists>vs. z = Fun (shp f) vs \<and> length vs = length ss"
    proof -
      have sharp_step: "(sharp_term shp (Fun f us),z)
          \<in> csdp_step shp \<mu> (set Rs)" using step.hyps(2) unfolding y by simp
      from sharp_csdp_step_imp_csnrstep[OF wf fresh marked_inj sharp_step]
      obtain u where z: "z = sharp_term shp u"
        and nonroot: "(Fun f us,u) \<in> csnrstep \<mu> (set Rs)" by blast
      from nonroot obtain vs where u: "u = Fun f vs"
        and len: "length vs = length us" by (elim csnrstep_FunE, blast)
      with z us_len show ?thesis by auto
    qed
    show ?case
      by (intro conjI rtrancl_trans[OF prefix one] z_SN z_shape)
  qed
  then show ?thesis by blast
qed

lemma SN_sharp_csdp_imp_SN_csstep_extended_basic:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_mu: "\<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {Fun (shp f) ss}"
  shows "SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
proof (rule ccontr)
  assume notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
  have undef: "\<not> defined (set Rs) (shp f,length ss)" by (rule fresh)
  from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf undef notSN]
  obtain j where j: "j < length ss"
    and active: "j \<in> \<mu> (shp f,length ss)"
    and notSN_j: "\<not> SN_on (csstep \<mu> (set Rs)) {ss ! j}" by blast
  have active_orig: "j \<in> \<mu> (f,length ss)" using active marked_mu by simp
  from SN_sharp_csdp_imp_SN_active_arg[OF j active_orig SN]
    notSN_j show False by contradiction
qed

theorem finite_min_csr_dpp_extended_basic_redpair:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<forall>(l,r)\<in>P. \<forall>f ss.
      (l = Fun (shp f) ss \<or> r = Fun (shp f) ss) \<longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pairs_in: "P \<subseteq> T"
    and pair_shape: "\<forall>(l,r)\<in>P.
      (\<exists>f ls. l = Fun (shp f) ls) \<and>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and rules_NS: "U \<union> ce_trs cn \<subseteq> NS"
    and fin: "finite_min_csr_dpp shp \<mu> (P - S) (set Rs)"
  shows "finite_min_csr_dpp shp \<mu> P (set Rs)"
proof -
  interpret rp: compat_redpair_order S NS by (rule redpair)
  have rewrite_NS: "rstep (U \<union> ce_trs cn) \<subseteq> NS"
    by (rule subset_trans[OF rstep_mono[OF rules_NS] rp.rstep_NS])
  have rewrite_star_NS: "(rstep (U \<union> ce_trs cn))\<^sup>* \<subseteq> NS"
  proof (rule subrelI)
    fix x y
    assume steps: "(x,y) \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    show "(x,y) \<in> NS" using steps
    proof (induct rule: rtrancl_induct)
      case base
      show ?case using rp.refl_NS unfolding refl_on_def by blast
    next
      case (step y z)
      have yz: "(y,z) \<in> NS" using rewrite_NS step.hyps(2) by blast
      from transD[OF rp.trans_NS step.hyps(3) yz] show ?case .
    qed
  qed
  show ?thesis
  proof (rule finite_min_csr_dpp_redpair_simulation[
      OF redpair orient _ fin])
    fix s t \<sigma>
    assume pair: "\<And>k. (s k,t k) \<in> P"
      and target_SN: "\<And>k. SN_on (csdp_step shp \<mu> (set Rs))
        {t k \<cdot> \<sigma> k}"
      and steps: "\<And>k. (t k \<cdot> \<sigma> k,
        s (Suc k) \<cdot> \<sigma> (Suc k))
        \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
    let ?\<tau> = "\<lambda>k. i2_subst (s k) (\<sigma> k)"
    have between: "(t k \<cdot> ?\<tau> k,
        s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS" for k
    proof -
      from pair_shape pair[of k] obtain f ls g rs where
        sk: "s k = Fun (shp f) ls" and tk: "t k = Fun (shp g) rs" by auto
      have mu_g: "\<mu> (shp g,length rs) = \<mu> (g,length rs)"
        using marked_mu pair[of k] tk by blast
      have target_form: "t k \<cdot> \<sigma> k =
          Fun (shp g) (map (\<lambda>u. u \<cdot> \<sigma> k) rs)"
        unfolding tk by simp
      have mu_g_sub:
          "\<mu> (shp g,length (map (\<lambda>u. u \<cdot> \<sigma> k) rs)) =
           \<mu> (g,length (map (\<lambda>u. u \<cdot> \<sigma> k) rs))"
        using mu_g by simp
      have target_cs_SN: "SN_on (csstep \<mu> (set Rs))
          {t k \<cdot> \<sigma> k}"
        unfolding target_form
        by (rule SN_sharp_csdp_imp_SN_csstep_extended_basic[
          OF fresh mu_g_sub target_SN[of k, unfolded target_form]])
      have pair_T: "(s k,t k) \<in> T" using pairs_in pair[of k] by blast
      have target_local: "(t k \<cdot> ?\<tau> k,
          i2_bracket (t k) (\<sigma> k))
          \<in> (rstep (ce_trs cn))\<^sup>*"
        by (rule i2_lhs_subst_to_bracket_rsteps[
          OF eb_active_variables[OF pair_T]])
      have target_roots: "\<And>p. p \<in> mu_fun_poss \<mu> (t k) \<Longrightarrow>
          root (t k |_ p) \<in> Some ` \<Delta>"
      proof -
        fix p
        assume p: "p \<in> mu_fun_poss \<mu> (t k)"
        from mu_fun_poss_imp_fun_poss[OF p] obtain h us where
          at: "t k |_ p = Fun h us" using fun_poss_fun_conv by blast
        have root: "root (t k |_ p) = Some (h,length us)" unfolding at by simp
        have "(h,length us) \<in> csr_u3_delta (set Rs) U"
          by (rule csr_u3_root_rules_closed_delta[
            OF closed_rhs[OF pair_T] p root])
        then show "root (t k |_ p) \<in> Some ` \<Delta>"
          unfolding delta root by blast
      qed
      have target_I: "i2 (t k \<cdot> \<sigma> k) =
          i2_bracket (t k) (\<sigma> k)"
        by (rule i2_equals_bracket[OF target_cs_SN target_roots])
      have target_to_I: "(t k \<cdot> ?\<tau> k,
          i2 (t k \<cdot> \<sigma> k))
          \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
      proof -
        have mono: "(rstep (ce_trs cn))\<^sup>* \<subseteq>
            (rstep (U \<union> ce_trs cn))\<^sup>*"
          by (rule rtrancl_mono, rule rstep_mono, simp)
        show ?thesis unfolding target_I
          by (rule mono[THEN subsetD, OF target_local])
      qed
      have transformed_steps: "(i2 (t k \<cdot> \<sigma> k),
          i2 (s (Suc k) \<cdot> \<sigma> (Suc k)))
          \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
        unfolding tk
        apply (rule i2_sharp_csdp_steps_extended_basic[
          where shp=shp and f=g and ss="map (\<lambda>x. x \<cdot> \<sigma> k) rs"])
             apply (rule fresh)
            apply (rule marked_inj)
           using mu_g apply simp
          apply simp
         using target_SN[of k] unfolding tk apply simp
        using steps[of k] unfolding tk apply simp
        done
      have next_dp_SN: "SN_on (csdp_step shp \<mu> (set Rs))
          {s (Suc k) \<cdot> \<sigma> (Suc k)}"
      proof (rule ccontr)
        assume notSN: "\<not> SN_on (csdp_step shp \<mu> (set Rs))
            {s (Suc k) \<cdot> \<sigma> (Suc k)}"
        from steps_notSN_on_source[OF steps[of k] notSN]
          target_SN[of k] show False by contradiction
      qed
      from pair_shape pair[of "Suc k"] obtain h us where
        next_s: "s (Suc k) = Fun (shp h) us" by auto
      have mu_h: "\<mu> (shp h,length us) = \<mu> (h,length us)"
        using marked_mu pair[of "Suc k"] next_s by blast
      have next_form: "s (Suc k) \<cdot> \<sigma> (Suc k) =
          Fun (shp h) (map (\<lambda>u. u \<cdot> \<sigma> (Suc k)) us)"
        unfolding next_s by simp
      have mu_h_sub:
          "\<mu> (shp h,length (map (\<lambda>u. u \<cdot> \<sigma> (Suc k)) us)) =
           \<mu> (h,length (map (\<lambda>u. u \<cdot> \<sigma> (Suc k)) us))"
        using mu_h by simp
      have next_cs_SN: "SN_on (csstep \<mu> (set Rs))
          {s (Suc k) \<cdot> \<sigma> (Suc k)}"
        unfolding next_form
        by (rule SN_sharp_csdp_imp_SN_csstep_extended_basic[
          OF fresh mu_h_sub next_dp_SN[unfolded next_form]])
      have next_pair_T: "(s (Suc k),t (Suc k)) \<in> T"
        using pairs_in pair[of "Suc k"] by blast
      have next_project0: "(i2 (s (Suc k) \<cdot> \<sigma> (Suc k)),
          i2_bracket (s (Suc k)) (\<sigma> (Suc k)))
          \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
        by (rule i2_projects_to_bracket[OF next_cs_SN])
      have next_bracket: "i2_bracket (s (Suc k)) (\<sigma> (Suc k)) =
          s (Suc k) \<cdot> ?\<tau> (Suc k)"
        by (rule i2_bracket_as_subst[OF lhs_partition[OF next_pair_T]])
      have next_project: "(i2 (s (Suc k) \<cdot> \<sigma> (Suc k)),
          s (Suc k) \<cdot> ?\<tau> (Suc k))
          \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
      proof -
        have mono: "(csstep \<mu> (ce_trs cn))\<^sup>* \<subseteq>
            (rstep (U \<union> ce_trs cn))\<^sup>*"
        proof (rule rtrancl_mono)
          show "csstep \<mu> (ce_trs cn) \<subseteq>
              rstep (U \<union> ce_trs cn)"
            by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
        qed
        have projected: "(i2 (s (Suc k) \<cdot> \<sigma> (Suc k)),
            i2_bracket (s (Suc k)) (\<sigma> (Suc k)))
            \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
          by (rule mono[THEN subsetD, OF next_project0])
        show ?thesis using projected next_bracket by simp
      qed
      have all_steps: "(t k \<cdot> ?\<tau> k,
          s (Suc k) \<cdot> ?\<tau> (Suc k))
          \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
        by (rule rtrancl_trans[OF target_to_I
          rtrancl_trans[OF transformed_steps next_project]])
      show ?thesis by (rule rewrite_star_NS[THEN subsetD, OF all_steps])
    qed
    show "\<exists>\<tau>. \<forall>k.
      (t k \<cdot> \<tau> k,s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
      by (rule exI[of _ ?\<tau>], use between in blast)
  qed
qed

end

theorem finite_min_csr_dpp_muterm_extended_basic_redpair:
  fixes Rs :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) rules)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
    and U P :: "((('f,'l) lab),'v) trs"
  assumes wf: "wf_trs (set Rs)"
    and closed: "muterm_extended_basic_ur_closed
      (set Rs) U \<mu> P {}"
    and side: "muterm_extended_basic_side_conditions \<mu> P U"
    and fresh: "\<And>f n. \<not> defined (set Rs) (Sharp f,n)"
    and marked_mu: "\<forall>(l,r)\<in>P. \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      \<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pair_shape: "\<forall>(l,r)\<in>P.
      (\<exists>f ls. l = Fun (Sharp f) ls) \<and>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    and U_NS: "U \<subseteq> NS"
    and ce: "ce_compatible NS"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P - S) (set Rs)"
  shows "finite_min_csr_dpp Sharp \<mu> P (set Rs)"
proof (cases "P = {}")
  case True
  with fin show ?thesis by simp
next
  case False
  then obtain dp where dp: "dp \<in> P" by blast
  from pair_shape dp obtain f us where lhs: "fst dp = Fun (Sharp f) us"
    by (cases dp, auto)
  obtain n where ce_bound:
    "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> NS"
  proof (rule ce_compatibleE[OF ce])
    fix n
    assume bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> NS"
    show thesis by (rule that[OF bound])
  qed
  let ?cn = "(Sharp f,n)"
  have ce_NS: "ce_trs ?cn \<subseteq> NS" by (rule ce_bound, simp)
  have rules_NS: "U \<union> ce_trs ?cn \<subseteq> NS" using U_NS ce_NS by auto
  have U_R: "U \<subseteq> set Rs"
    using closed unfolding muterm_extended_basic_ur_closed_def by blast
  have nc: "\<forall>(l,r)\<in>P. is_Fun r"
    using side unfolding muterm_extended_basic_side_conditions_def
      muterm_extended_basic_noncollapsing_def by blast
  let ?T = "P \<union> U"
  have closed_rhs: "\<And>l r. (l,r) \<in> ?T \<Longrightarrow>
      csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
  proof -
    fix l r
    assume lr: "(l,r) \<in> ?T"
    have seed: "(l,r) \<in>
        {dp \<in> P. is_Fun (snd dp)} \<union> {} \<union> U"
      using lr nc by auto
    from closed have closure:
        "\<forall>lr\<in>{dp \<in> P. is_Fun (snd dp)} \<union> {} \<union> U.
          csr_u3_root_rules_closed (set Rs) U (snd lr)
            (mu_fun_poss \<mu> (snd lr))"
      unfolding muterm_extended_basic_ur_closed_def by (rule conjunct2)
    from closure[rule_format, OF seed] show
      "csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
      by simp
  qed
  have cons: "rhs_mu_vars_condition \<mu> ?T"
    using side unfolding muterm_extended_basic_side_conditions_def by blast
  have lhs_part: "\<And>l r. (l,r) \<in> ?T \<Longrightarrow>
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    using side unfolding muterm_extended_basic_side_conditions_def by blast
  have lhs_T: "\<And>l r. (l,r) \<in> ?T \<Longrightarrow> is_Fun l"
  proof -
    fix l r
    assume lr: "(l,r) \<in> ?T"
    show "is_Fun l"
    proof (cases "(l,r) \<in> P")
      case True
      from pair_shape True show ?thesis by auto
    next
      case False
      with lr have "(l,r) \<in> U" by blast
      with U_R have "(l,r) \<in> set Rs" by blast
      with wf show ?thesis unfolding wf_trs_def by (cases l, auto)
    qed
  qed
  interpret L: muterm_i2_extended_basic Rs \<mu>
      "csr_u3_delta (set Rs) U" ?cn U ?T
  proof
    show "wf_trs (set Rs)" by (rule wf)
  next
    show "csr_u3_delta (set Rs) U = csr_u3_delta (set Rs) U" by simp
  next
    fix l r
    assume lr: "(l,r) \<in> ?T"
    show "csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
      by (rule closed_rhs[OF lr])
  next
    show "rhs_mu_vars_condition \<mu> ?T" by (rule cons)
  next
    fix l r
    assume lr: "(l,r) \<in> ?T"
    show "mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
      by (rule lhs_part[OF lr])
  next
    show "U \<subseteq> ?T" by simp
  next
    fix l r
    assume lr: "(l,r) \<in> ?T"
    show "is_Fun l" by (rule lhs_T[OF lr])
  qed
  show ?thesis
    by (rule L.finite_min_csr_dpp_extended_basic_redpair[
      OF fresh inj_Sharp marked_mu redpair orient _ pair_shape
        rules_NS fin], simp)
qed

definition muterm_extended_basic_redpair_proc where
  "muterm_extended_basic_redpair_proc J \<mu> rp Premove U dpp =
    check_return (do {
      rel_impl_redpair rp;
      let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
      check (csr_sharp_pairs_check (dpp_ops.pairs J dpp))
        (showsl_lit (STR ''extended-basic processor requires marked pairs''));
      check (muterm_marked_mu_pairs_check \<mu> (dpp_ops.pairs J dpp))
        (showsl_lit (STR ''marked replacement-map entries differ from their source symbols''));
      check (muterm_extended_basic_ur_closed_check
          (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp) [])
        (showsl_lit (STR ''supplied rules are not a closed extended-basic set''));
      muterm_extended_basic_side_conditions_check \<mu>
        (dpp_ops.pairs J dpp) U;
      rel_impl.ce_compat rp;
      rel_impl_ns rp (U @ pns);
      rel_impl_s rp ps
    }) (dpp_spec.delete_pairs J dpp Premove)"

lemma muterm_extended_basic_redpair_proc_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_extended_basic_redpair_proc J \<mu> rp Premove U dpp =
      return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove" by auto
  from proc[unfolded muterm_extended_basic_redpair_proc_def Let_def
      split,simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and shape: "csr_sharp_pairs_check (pairs dpp)"
    and marked: "muterm_marked_mu_pairs_check \<mu> (pairs dpp)"
    and closed: "muterm_extended_basic_ur_closed_check
      (rules dpp) U \<mu> (pairs dpp) []"
    and side: "isOK (muterm_extended_basic_side_conditions_check
      \<mu> (pairs dpp) U)"
    and ce: "isOK (rel_impl.ce_compat rp)"
    and weak: "isOK (rel_impl_ns rp (U @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def,simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)" by auto
  let ?all = "ps @ U @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST" by blast
  have all_rel': "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule spec[OF all_rel])
  obtain S NS NST where rel_prop: "rel_impl_prop rp ?all S NS NST"
    using all_rel' by presburger
  from rel_prop strict weak subst sn standard ce
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
    and pns_NS: "set pns \<subseteq> NS"
    and S_NS: "S \<subseteq> NS"
    and S_NS_comp: "S O NS \<subseteq> S"
    and NS_S_comp: "NS O S \<subseteq> S"
    and ctxt_NS: "ctxt.closed NS"
    and trans_NS: "trans NS"
    and refl_NS: "refl NS"
    and subst_NS: "subst.closed NS"
    and trans_S: "trans S"
    and irrefl_S: "irrefl S"
    and subst_S: "subst.closed S"
    and SN_S: "SN S"
    and ce_NS: "ce_compatible NS"
    by (auto simp: rel_impl_list)
  have redpair: "compat_redpair_order S NS" by (unfold_locales; fact)
  have orient: "set (pairs dpp) \<subseteq> S \<union> NS"
    using strict_S pns_NS unfolding ps pns by auto
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have sub: "set (pairs dpp) - S \<subseteq>
      set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have fin_S: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - S) (set (rules dpp))"
    by (rule finite_min_csr_dpp_mono_pairs[
      OF sub fin[unfolded pairs' rules']])
  have shape_sem: "\<forall>(l,r)\<in>set (pairs dpp).
      (\<exists>f ls. l = Fun (Sharp f) ls) \<and>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    by (rule csr_sharp_pairs_check_sound[OF shape])
  have marked_sem: "\<forall>(l,r)\<in>set (pairs dpp). \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      mu_of \<mu> (Sharp f,length ss) = mu_of \<mu> (f,length ss)"
    by (rule muterm_marked_mu_pairs_check_sound[OF marked])
  have closed_sem: "muterm_extended_basic_ur_closed
      (set (rules dpp)) (set U) (mu_of \<mu>) (set (pairs dpp)) {}"
    using muterm_extended_basic_ur_closed_check_sound[OF closed] by simp
  have side_sem: "muterm_extended_basic_side_conditions (mu_of \<mu>)
      (set (pairs dpp)) (set U)"
    by (rule muterm_extended_basic_side_conditions_check_sound[OF side])
  show ?thesis
    by (rule finite_min_csr_dpp_muterm_extended_basic_redpair[
      OF wf closed_sem side_sem fresh marked_sem redpair orient shape_sem
        U_NS ce_NS fin_S])
qed

text \<open>
  Historical experiments below explored stronger step-local [i2] lemmas.  They
  isolate the sound typed collapsing/noncollapsing cases needed by the native
  MU-TERM reduction triple.  The unrelated strong-chain experiments remain
  disabled below.
\<close>

context muterm_i2
begin

lemma i2_not_SN_identity:
  assumes "\<not> SN_on (csstep \<mu> (set Rs)) {t}"
  shows "i2 t = t"
  using assms by (cases t) (simp_all add: i2_Fun)

lemma i2_collapsing_pair_redpair_order:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "rstep (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and lhs_partition: "\<And>l x. (l,Var x) \<in> P \<Longrightarrow>
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and source_SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and source_not_SN: "\<And>x l y \<sigma>. (l,Var y) \<in> P \<Longrightarrow>
      s = l \<cdot> \<sigma> \<Longrightarrow> x = \<sigma> y \<Longrightarrow>
      (x,t) \<in> rrstep B \<Longrightarrow>
      \<not> SN_on (csstep \<mu> (set Rs)) {x}"
    and target_not_SN: "\<not> SN_on (csstep \<mu> (set Rs)) {t}"
    and pair_step: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
  shows "(i2 s,i2 t) \<in> Rgt \<union> Rge \<and>
    ((i2 s,i2 t) \<notin> Rgt \<longrightarrow>
      (\<exists>x. muterm_collapsing_rrstep (P - Rgt) s x \<and>
        (x,t) \<in> rrstep B))"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from pair_step obtain x l y \<sigma> where pair: "(l,Var y) \<in> P"
    and s: "s = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
    and bridge: "(x,t) \<in> rrstep B"
    unfolding muterm_collapsing_rrstep_def by auto
  from bridge obtain a b \<theta> where ab: "(a,b) \<in> B"
    and x': "x = a \<cdot> \<theta>" and t: "t = b \<cdot> \<theta>"
    unfolding rrstep_def' by auto
  have x_not: "\<not> SN_on (csstep \<mu> (set Rs)) {x}"
    by (rule source_not_SN[OF pair s x bridge])
  have ix: "i2 x = x" by (rule i2_not_SN_identity[OF x_not])
  have it: "i2 t = t" by (rule i2_not_SN_identity[OF target_not_SN])
  let ?\<tau> = "i2_subst l \<sigma>"
  have tau_y: "?\<tau> y = \<sigma> y"
    unfolding i2_subst_def using ix[unfolded x] by auto
  from i2_projects_to_bracket[OF source_SN[unfolded s]]
  have project0: "(i2 (l \<cdot> \<sigma>),i2_bracket l \<sigma>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
  have bracket: "i2_bracket l \<sigma> = l \<cdot> ?\<tau>"
    by (rule i2_bracket_as_subst[OF lhs_partition[OF pair]])
  have cs_sub: "csstep \<mu> (ce_trs cn) \<subseteq>
      rstep (U \<union> ce_trs cn)"
    by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
  have project_steps: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>)
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    using project0 unfolding bracket
    by (rule rtrancl_mono[OF cs_sub, THEN subsetD])
  have project_star: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF project_steps])
  have project: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge"
    using project_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
  have bridge_weak: "(x,t) \<in> Rge"
  proof -
    from bridges_order ab have "(a,b) \<in> Rge" by auto
    then have "(a \<cdot> \<theta>,b \<cdot> \<theta>) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS])
    then show ?thesis unfolding x' t .
  qed
  from pairs_order pair have pair_ord: "(l,Var y) \<in> Rgt \<union> Rge" by auto
  show ?thesis
  proof (cases "(l,Var y) \<in> Rgt")
    case True
    have strict0: "(l \<cdot> ?\<tau>,Var y \<cdot> ?\<tau>) \<in> Rgt"
      by (rule subst.closedD[OF rp.subst_S True])
    have strict1: "(i2 (l \<cdot> \<sigma>),?\<tau> y) \<in> Rgt"
      using rp.compat_NS_S project strict0 by auto
    have strict2: "(i2 (l \<cdot> \<sigma>),t) \<in> Rgt"
      using rp.compat_S_NS strict1[unfolded tau_y x[symmetric]] bridge_weak
      by auto
    show ?thesis unfolding s it using strict2 by auto
  next
    case False
    with pair_ord have weak0: "(l,Var y) \<in> Rge" by auto
    have weak1: "(l \<cdot> ?\<tau>,Var y \<cdot> ?\<tau>) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS weak0])
    have weak2: "(i2 (l \<cdot> \<sigma>),?\<tau> y) \<in> Rge"
      using rp.trans_NS_point project weak1 by auto
    have weak3: "(i2 (l \<cdot> \<sigma>),t) \<in> Rge"
      by (rule rp.trans_NS_point[
        OF weak2[unfolded tau_y x[symmetric]] bridge_weak])
    have pair_residual: "(l,Var y) \<in> P - Rgt" using pair False by auto
    have collapsing_residual:
        "muterm_collapsing_rrstep (P - Rgt) s x"
      unfolding muterm_collapsing_rrstep_def
      using pair_residual s x by blast
    show ?thesis
    proof (intro conjI)
      show "(i2 s,i2 t) \<in> Rgt \<union> Rge"
        unfolding s it using weak3 by simp
      show "(i2 s,i2 t) \<notin> Rgt \<longrightarrow>
        (\<exists>x. muterm_collapsing_rrstep (P - Rgt) s x \<and>
          (x,t) \<in> rrstep B)"
        using collapsing_residual bridge by blast
    qed
  qed
qed

end

context muterm_i2_extended_basic
begin

lemma i2_noncollapsing_pair_extended_basic_redpair_order:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<And>f n. \<mu> (shp f,n) = \<mu> (f,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "rstep (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and pairs_in: "P \<subseteq> T"
    and pair_shape: "\<forall>(l,r)\<in>P.
      (\<exists>f ls. l = Fun (shp f) ls) \<and>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
    and target_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
    and pair_step: "muterm_noncollapsing_rrstep P s t"
  shows "(i2 s,i2 t) \<in> Rgt \<union> Rge \<and>
    ((i2 s,i2 t) \<notin> Rgt \<longrightarrow>
      muterm_noncollapsing_rrstep (P - Rgt) s t)"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from pair_step obtain l r \<sigma> where pair: "(l,r) \<in> P"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
  from pair_shape pair obtain f ls g rs where
    l: "l = Fun (shp f) ls" and r: "r = Fun (shp g) rs" by auto
  have source_form: "s = Fun (shp f) (map (\<lambda>u. u \<cdot> \<sigma>) ls)"
    unfolding s l by simp
  have source_cs_SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    unfolding source_form
    by (rule SN_sharp_csdp_imp_SN_csstep_extended_basic[
      OF fresh marked_mu source_SN[unfolded source_form]])
  have target_form: "t = Fun (shp g) (map (\<lambda>u. u \<cdot> \<sigma>) rs)"
    unfolding t r by simp
  have target_cs_SN: "SN_on (csstep \<mu> (set Rs)) {t}"
    unfolding target_form
    by (rule SN_sharp_csdp_imp_SN_csstep_extended_basic[
      OF fresh marked_mu target_SN[unfolded target_form]])
  have pair_T: "(l,r) \<in> T" by (rule pairs_in[THEN subsetD, OF pair])
  let ?\<tau> = "i2_subst l \<sigma>"
  from i2_projects_to_bracket[OF source_cs_SN[unfolded s]]
  have source0: "(i2 (l \<cdot> \<sigma>),i2_bracket l \<sigma>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
  have lhs_bracket: "i2_bracket l \<sigma> = l \<cdot> ?\<tau>"
    by (rule i2_bracket_as_subst[OF lhs_partition[OF pair_T]])
  have source_ce: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>)
      \<in> (rstep (ce_trs cn))\<^sup>*"
    using source0 unfolding lhs_bracket
    by (rule rtrancl_mono[OF csstep_subset_rstep, THEN subsetD])
  have target_ce: "(r \<cdot> ?\<tau>,i2_bracket r \<sigma>)
      \<in> (rstep (ce_trs cn))\<^sup>*"
    by (rule i2_lhs_subst_to_bracket_rsteps[
      OF eb_active_variables[OF pair_T]])
  have rhs_roots: "\<And>p. p \<in> mu_fun_poss \<mu> r \<Longrightarrow>
      root (r |_ p) \<in> Some ` \<Delta>"
  proof -
    fix p
    assume p: "p \<in> mu_fun_poss \<mu> r"
    from mu_fun_poss_imp_fun_poss[OF p] obtain h us where
      at: "r |_ p = Fun h us" using fun_poss_fun_conv by blast
    have root: "root (r |_ p) = Some (h,length us)" unfolding at by simp
    have "(h,length us) \<in> csr_u3_delta (set Rs) U"
      by (rule csr_u3_root_rules_closed_delta[
        OF closed_rhs[OF pair_T] p root])
    then show "root (r |_ p) \<in> Some ` \<Delta>"
      unfolding delta root by blast
  qed
  have rhs_I: "i2 (r \<cdot> \<sigma>) = i2_bracket r \<sigma>"
    by (rule i2_equals_bracket[OF target_cs_SN[unfolded t] rhs_roots])
  have ce_sub: "rstep (ce_trs cn) \<subseteq> rstep (U \<union> ce_trs cn)"
    by (rule rstep_mono, simp)
  have source_steps: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>)
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    by (rule rtrancl_mono[OF ce_sub, THEN subsetD, OF source_ce])
  have target_steps: "(r \<cdot> ?\<tau>,i2 (r \<cdot> \<sigma>))
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    unfolding rhs_I
    by (rule rtrancl_mono[OF ce_sub, THEN subsetD, OF target_ce])
  have source_star: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF source_steps])
  have target_star: "(r \<cdot> ?\<tau>,i2 (r \<cdot> \<sigma>)) \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF target_steps])
  have source_weak: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge"
    using source_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
  have target_weak: "(r \<cdot> ?\<tau>,i2 (r \<cdot> \<sigma>)) \<in> Rge"
    using target_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
  from pairs_order pair have pair_ord: "(l,r) \<in> Rgt \<union> Rge" by auto
  show ?thesis
  proof (cases "(l,r) \<in> Rgt")
    case True
    have middle: "(l \<cdot> ?\<tau>,r \<cdot> ?\<tau>) \<in> Rgt"
      by (rule subst.closedD[OF rp.subst_S True])
    have strict: "(i2 (l \<cdot> \<sigma>),i2 (r \<cdot> \<sigma>)) \<in> Rgt"
      using rp.compat_NS_S rp.compat_S_NS source_weak middle target_weak
      by auto
    show ?thesis unfolding s t using strict by auto
  next
    case False
    with pair_ord have weak: "(l,r) \<in> Rge" by auto
    have middle: "(l \<cdot> ?\<tau>,r \<cdot> ?\<tau>) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS weak])
    have total: "(i2 (l \<cdot> \<sigma>),i2 (r \<cdot> \<sigma>)) \<in> Rge"
      using rp.trans_NS_point source_weak middle target_weak by auto
    have pair_residual: "(l,r) \<in> P - Rgt" using pair False by auto
    have step_residual: "muterm_noncollapsing_rrstep (P - Rgt) s t"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def'
      using pair_residual s t r by blast
    show ?thesis
    proof (intro conjI)
      show "(i2 s,i2 t) \<in> Rgt \<union> Rge"
        unfolding s t using total by simp
      show "(i2 s,i2 t) \<notin> Rgt \<longrightarrow>
        muterm_noncollapsing_rrstep (P - Rgt) s t"
        using step_residual by blast
    qed
  qed
qed

(* The following tempting step-local statement is false.  In the collapsing
   case, i2 (a \<cdot> theta) = a \<cdot> theta does not imply that every active
   value selected by i2_subst a theta is unchanged.  Keep the failed attempt
   here as a warning until it is replaced by a genuinely chain-sensitive
   construction.

text \<open>
  The collapsing case uses the exact bridge source.  Since that entire hidden
  source is fixed by @{const i2}, structural injectivity fixes precisely the
  active substitution values needed by @{const i2_subst}; inactive values are
  left unchanged by definition.  Thus the bridge can be composed with the
  interpreted collapsing pair without imposing ordinary conservativity on
  the generated macro pair.
\<close>

lemma i2_collapsing_pair_extended_basic_redpair_order:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<And>f n. \<mu> (shp f,n) = \<mu> (f,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "rstep (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and bridges_in: "B \<subseteq> T"
    and pair_lhs_shape: "\<forall>(l,r)\<in>P. \<exists>f ls. l = Fun (shp f) ls"
    and bridge_rhs_shape: "\<forall>(l,r)\<in>B. \<exists>g rs. r = Fun (shp g) rs"
    and collapsing_lhs_partition: "\<And>l x. (l,Var x) \<in> P \<Longrightarrow>
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and source_hidden_not_SN: "\<And>x l y \<sigma>. (l,Var y) \<in> P \<Longrightarrow>
      s = l \<cdot> \<sigma> \<Longrightarrow> x = \<sigma> y \<Longrightarrow>
      (x,t) \<in> rrstep B \<Longrightarrow>
      \<not> SN_on (csstep \<mu> (set Rs)) {x}"
    and source_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
    and target_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
    and pair_step: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
  shows "(i2 s,i2 t) \<in> Rgt \<union> Rge \<and>
    ((i2 s,i2 t) \<notin> Rgt \<longrightarrow>
      (\<exists>x. muterm_collapsing_rrstep (P - Rgt) s x \<and>
        (x,t) \<in> rrstep B))"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from pair_step obtain x l y \<sigma> where pair: "(l,Var y) \<in> P"
    and s: "s = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
    and bridge: "(x,t) \<in> rrstep B"
    unfolding muterm_collapsing_rrstep_def by auto
  from bridge obtain a b \<theta> where ab: "(a,b) \<in> B"
    and x': "x = a \<cdot> \<theta>" and t: "t = b \<cdot> \<theta>"
    unfolding rrstep_def' by auto
  from pair_lhs_shape pair obtain f ls where l: "l = Fun (shp f) ls" by auto
  from bridge_rhs_shape ab obtain g rs where b: "b = Fun (shp g) rs" by auto
  have source_form: "s = Fun (shp f) (map (\<lambda>u. u \<cdot> \<sigma>) ls)"
    unfolding s l by simp
  have source_cs_SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    unfolding source_form
    by (rule SN_sharp_csdp_imp_SN_csstep_extended_basic[
      OF fresh marked_mu source_SN[unfolded source_form]])
  have target_form: "t = Fun (shp g) (map (\<lambda>u. u \<cdot> \<theta>) rs)"
    unfolding t b by simp
  have target_cs_SN: "SN_on (csstep \<mu> (set Rs)) {t}"
    unfolding target_form
    by (rule SN_sharp_csdp_imp_SN_csstep_extended_basic[
      OF fresh marked_mu target_SN[unfolded target_form]])
  have x_not: "\<not> SN_on (csstep \<mu> (set Rs)) {x}"
    by (rule source_hidden_not_SN[OF pair s x bridge])
  have ix: "i2 x = x" by (rule i2_not_SN_identity[OF x_not])
  let ?\<sigma>' = "i2_subst l \<sigma>"
  let ?\<theta>' = "i2_subst a \<theta>"
  have sigma_y: "?\<sigma>' y = \<sigma> y"
    unfolding i2_subst_def using ix[unfolded x] by auto
  from i2_projects_to_bracket[OF source_cs_SN[unfolded s]]
  have source0: "(i2 (l \<cdot> \<sigma>),i2_bracket l \<sigma>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
  have lhs_bracket: "i2_bracket l \<sigma> = l \<cdot> ?\<sigma>'"
    by (rule i2_bracket_as_subst[OF collapsing_lhs_partition[OF pair]])
  have cs_sub: "csstep \<mu> (ce_trs cn) \<subseteq>
      rstep (U \<union> ce_trs cn)"
    by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
  have source_steps: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<sigma>')
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    using source0 unfolding lhs_bracket
    by (rule rtrancl_mono[OF cs_sub, THEN subsetD])
  have source_star: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<sigma>') \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF source_steps])
  have source_weak: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<sigma>') \<in> Rge"
    using source_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
  have bridge_T: "(a,b) \<in> T" by (rule bridges_in[THEN subsetD, OF ab])
  have target0: "(b \<cdot> ?\<theta>',i2_bracket b \<theta>)
      \<in> (rstep (ce_trs cn))\<^sup>*"
    by (rule i2_lhs_subst_to_bracket_rsteps[
      OF eb_active_variables[OF bridge_T]])
  have target_roots: "\<And>p. p \<in> mu_fun_poss \<mu> b \<Longrightarrow>
      root (b |_ p) \<in> Some ` \<Delta>"
  proof -
    fix p
    assume p: "p \<in> mu_fun_poss \<mu> b"
    from mu_fun_poss_imp_fun_poss[OF p] obtain h us where
      at: "b |_ p = Fun h us" using fun_poss_fun_conv by blast
    have root: "root (b |_ p) = Some (h,length us)" unfolding at by simp
    have "(h,length us) \<in> csr_u3_delta (set Rs) U"
      by (rule csr_u3_root_rules_closed_delta[
        OF closed_rhs[OF bridge_T] p root])
    then show "root (b |_ p) \<in> Some ` \<Delta>"
      unfolding delta root by blast
  qed
  have target_I: "i2 (b \<cdot> \<theta>) = i2_bracket b \<theta>"
    by (rule i2_equals_bracket[OF target_cs_SN[unfolded t] target_roots])
  have ce_sub: "rstep (ce_trs cn) \<subseteq> rstep (U \<union> ce_trs cn)"
    by (rule rstep_mono, simp)
  have target_steps: "(b \<cdot> ?\<theta>',i2 (b \<cdot> \<theta>))
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    unfolding target_I
    by (rule rtrancl_mono[OF ce_sub, THEN subsetD, OF target0])
  have target_star: "(b \<cdot> ?\<theta>',i2 (b \<cdot> \<theta>)) \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF target_steps])
  have target_weak: "(b \<cdot> ?\<theta>',i2 (b \<cdot> \<theta>)) \<in> Rge"
    using target_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
  have bridge_weak: "(x,b \<cdot> ?\<theta>') \<in> Rge"
  proof -
    from bridges_order ab have "(a,b) \<in> Rge" by auto
    then have "(a \<cdot> ?\<theta>',b \<cdot> ?\<theta>') \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS])
    moreover have "a \<cdot> ?\<theta>' = x"
      unfolding i2_subst_def x' using ix by (induct a, auto)
    ultimately show ?thesis by simp
  qed
  from pairs_order pair have pair_ord: "(l,Var y) \<in> Rgt \<union> Rge" by auto
  show ?thesis
  proof (cases "(l,Var y) \<in> Rgt")
    case True
    have middle: "(l \<cdot> ?\<sigma>',Var y \<cdot> ?\<sigma>') \<in> Rgt"
      by (rule subst.closedD[OF rp.subst_S True])
    have strict0: "(i2 (l \<cdot> \<sigma>),x) \<in> Rgt"
      using rp.compat_NS_S source_weak middle
      unfolding sigma_y x by auto
    have strict1: "(i2 (l \<cdot> \<sigma>),b \<cdot> ?\<theta>') \<in> Rgt"
      using rp.compat_S_NS strict0 bridge_weak by auto
    have strict2: "(i2 (l \<cdot> \<sigma>),i2 (b \<cdot> \<theta>)) \<in> Rgt"
      using rp.compat_S_NS strict1 target_weak by auto
    show ?thesis unfolding s t using strict2 by auto
  next
    case False
    with pair_ord have weak_pair: "(l,Var y) \<in> Rge" by auto
    have middle: "(l \<cdot> ?\<sigma>',Var y \<cdot> ?\<sigma>') \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS weak_pair])
    have weak0: "(i2 (l \<cdot> \<sigma>),x) \<in> Rge"
      using rp.trans_NS_point source_weak middle
      unfolding sigma_y x by auto
    have weak1: "(i2 (l \<cdot> \<sigma>),b \<cdot> ?\<theta>') \<in> Rge"
      by (rule rp.trans_NS_point[OF weak0 bridge_weak])
    have weak2: "(i2 (l \<cdot> \<sigma>),i2 (b \<cdot> \<theta>)) \<in> Rge"
      by (rule rp.trans_NS_point[OF weak1 target_weak])
    have pair_residual: "(l,Var y) \<in> P - Rgt" using pair False by auto
    have collapsing_residual:
        "muterm_collapsing_rrstep (P - Rgt) s x"
      unfolding muterm_collapsing_rrstep_def
      using pair_residual s x by blast
    show ?thesis unfolding s t using weak2 collapsing_residual bridge by auto
  qed
qed

*)

lemma i2_collapsing_pair_extended_basic_redpair_order_fixed:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "rstep (U \<union> ce_trs cn) \<subseteq> Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and lhs_partition: "\<And>l x. (l,Var x) \<in> P \<Longrightarrow>
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and source_SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and hidden_not_SN: "\<And>x l y \<sigma>. (l,Var y) \<in> P \<Longrightarrow>
      s = l \<cdot> \<sigma> \<Longrightarrow> x = \<sigma> y \<Longrightarrow>
      (x,t) \<in> rrstep B \<Longrightarrow>
      \<not> SN_on (csstep \<mu> (set Rs)) {x}"
    and target_not_SN: "\<not> SN_on (csstep \<mu> (set Rs)) {t}"
    and pair_step: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
  shows "(i2 s,i2 t) \<in> Rgt \<union> Rge \<and>
    ((i2 s,i2 t) \<notin> Rgt \<longrightarrow>
      (\<exists>x. muterm_collapsing_rrstep (P - Rgt) s x \<and>
        (x,t) \<in> rrstep B))"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from pair_step obtain x l y \<sigma> where pair: "(l,Var y) \<in> P"
    and s: "s = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
    and bridge: "(x,t) \<in> rrstep B"
    unfolding muterm_collapsing_rrstep_def by auto
  have x_not: "\<not> SN_on (csstep \<mu> (set Rs)) {x}"
    by (rule hidden_not_SN[OF pair s x bridge])
  have ix: "i2 x = x" by (rule i2_not_SN_identity[OF x_not])
  have it: "i2 t = t" by (rule i2_not_SN_identity[OF target_not_SN])
  let ?\<tau> = "i2_subst l \<sigma>"
  have tau_y: "?\<tau> y = \<sigma> y"
    unfolding i2_subst_def using ix[unfolded x] by auto
  from i2_projects_to_bracket[OF source_SN[unfolded s]]
  have project0: "(i2 (l \<cdot> \<sigma>),i2_bracket l \<sigma>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
  have bracket: "i2_bracket l \<sigma> = l \<cdot> ?\<tau>"
    by (rule i2_bracket_as_subst[OF lhs_partition[OF pair]])
  have cs_sub: "csstep \<mu> (ce_trs cn) \<subseteq>
      rstep (U \<union> ce_trs cn)"
    by (rule subset_trans[OF csstep_subset_rstep], rule rstep_mono, simp)
  have project_steps: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>)
      \<in> (rstep (U \<union> ce_trs cn))\<^sup>*"
    using project0 unfolding bracket
    by (rule rtrancl_mono[OF cs_sub, THEN subsetD])
  have project_star: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF project_steps])
  have project: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?\<tau>) \<in> Rge"
    using project_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
  have bridge_weak: "(x,t) \<in> Rge"
  proof -
    from bridge obtain a b \<theta> where ab: "(a,b) \<in> B"
      and x': "x = a \<cdot> \<theta>" and t': "t = b \<cdot> \<theta>"
      unfolding rrstep_def' by auto
    from bridges_order ab have "(a,b) \<in> Rge" by auto
    then have "(a \<cdot> \<theta>,b \<cdot> \<theta>) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS])
    then show ?thesis unfolding x' t' .
  qed
  from pairs_order pair have pair_ord: "(l,Var y) \<in> Rgt \<union> Rge" by auto
  show ?thesis
  proof (cases "(l,Var y) \<in> Rgt")
    case True
    have middle: "(l \<cdot> ?\<tau>,Var y \<cdot> ?\<tau>) \<in> Rgt"
      by (rule subst.closedD[OF rp.subst_S True])
    have strict0': "(i2 (l \<cdot> \<sigma>),?\<tau> y) \<in> Rgt"
      using rp.compat_NS_S project middle by auto
    have strict0: "(i2 (l \<cdot> \<sigma>),x) \<in> Rgt"
      using strict0' tau_y unfolding x by simp
    have strict1: "(i2 (l \<cdot> \<sigma>),t) \<in> Rgt"
      using rp.compat_S_NS strict0 bridge_weak by auto
    have ordered: "(i2 s,i2 t) \<in> Rgt"
      using strict1 unfolding s it .
    show ?thesis using ordered by auto
  next
    case False
    with pair_ord have weak_pair: "(l,Var y) \<in> Rge" by auto
    have middle: "(l \<cdot> ?\<tau>,Var y \<cdot> ?\<tau>) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS weak_pair])
    have weak0': "(i2 (l \<cdot> \<sigma>),?\<tau> y) \<in> Rge"
      using rp.trans_NS_point project middle by auto
    have weak0: "(i2 (l \<cdot> \<sigma>),x) \<in> Rge"
      using weak0' tau_y unfolding x by simp
    have weak1: "(i2 (l \<cdot> \<sigma>),t) \<in> Rge"
      by (rule rp.trans_NS_point[OF weak0 bridge_weak])
    have pair_residual: "(l,Var y) \<in> P - Rgt" using pair False by auto
    have collapsing_residual:
        "muterm_collapsing_rrstep (P - Rgt) s x"
      unfolding muterm_collapsing_rrstep_def using pair_residual s x by blast
    have ordered: "(i2 s,i2 t) \<in> Rge"
      using weak1 unfolding s it .
    show ?thesis using ordered collapsing_residual bridge by auto
  qed
qed

text \<open>
  The preceding lemma is deliberately not an executable processor yet.  Its
  @{term target_not_SN} premise describes a nonterminating target of the
  source rewrite relation, whereas a minimal MU-TERM chain supplies rewrite
  termination of pair targets.  In particular, it cannot justify the false
  collapsing component of @{text "CSR_04/Ex1_GM03"}.  The production lift
  must reason about the strict deletion inside the typed chain simulation;
  replacing this premise by the chain's continuation nontermination, or by
  dropping target safety from the outer usable-rule check, would be unsound.
\<close>

end

(* Unused strong-chain experiments.
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
*)

end
