(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Innermost_Unhiding_Proofs
  imports
    "CSR_Checker_Extensions.CSR_Innermost_Switch"
    "CSR_Checker_Extensions.CSR_Improved_CSDP_Proofs"
begin

text \<open>
  MU-TERM's compressed unhiding component records a complete frozen RHS
  fragment together with every defined call reachable inside that fragment at
  replacement-map positions.  The additional safety condition below excludes
  an active path into a variable which was frozen in the source left-hand
  side.  Under this check, every newly exposed nonterminating call is a
  syntactic call represented by one of the supplied rules; no generic
  projection rule is required.
\<close>

definition muterm_frozen_root_on ::
  "'f mu \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool"
where
  "muterm_frozen_root_on \<mu> r h \<longleftrightarrow>
    (\<exists>p f ts i. p \<in> mu_fun_poss \<mu> r \<and> r |_ p = Fun f ts \<and>
      i < length ts \<and> i \<notin> \<mu> (f,length ts) \<and> h = ts ! i)"

lemma muterm_frozen_root_on_Fun:
  "muterm_frozen_root_on \<mu> (Fun f ts) h \<longleftrightarrow>
    (\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and> h = ts ! i) \<or>
    (\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_frozen_root_on \<mu> (ts ! i) h)"
proof
  assume root: "muterm_frozen_root_on \<mu> (Fun f ts) h"
  then obtain p g us j where p: "p \<in> mu_fun_poss \<mu> (Fun f ts)"
    and at: "Fun f ts |_ p = Fun g us" and j: "j < length us"
    and inactive: "j \<notin> \<mu> (g,length us)" and h: "h = us ! j"
    unfolding muterm_frozen_root_on_def by blast
  show "(\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and> h = ts ! i) \<or>
    (\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_frozen_root_on \<mu> (ts ! i) h)"
  proof (cases p)
    case Nil
    with at j inactive h show ?thesis by auto
  next
    case (Cons i q)
    from p Cons have ilen: "i < length ts" and ia: "i \<in> \<mu> (f,length ts)"
      and q: "q \<in> mu_fun_poss \<mu> (ts ! i)" by auto
    have qat: "ts ! i |_ q = Fun g us" using at Cons ilen by simp
    have "muterm_frozen_root_on \<mu> (ts ! i) h"
      unfolding muterm_frozen_root_on_def
      using q qat j inactive h by blast
    with ilen ia show ?thesis by blast
  qed
next
  assume split: "(\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and> h = ts ! i) \<or>
    (\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_frozen_root_on \<mu> (ts ! i) h)"
  show "muterm_frozen_root_on \<mu> (Fun f ts) h"
  proof (rule disjE[OF split])
    assume "\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and> h = ts ! i"
    then obtain i where i: "i < length ts" "i \<notin> \<mu> (f,length ts)"
      "h = ts ! i" by blast
    show ?thesis unfolding muterm_frozen_root_on_def
      by (intro exI[of _ "[]"] exI[of _ f] exI[of _ ts] exI[of _ i],
          use i in auto)
  next
    assume "\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_frozen_root_on \<mu> (ts ! i) h"
    then obtain i p g us j where i: "i < length ts" "i \<in> \<mu> (f,length ts)"
      and p: "p \<in> mu_fun_poss \<mu> (ts ! i)" and at: "ts ! i |_ p = Fun g us"
      and j: "j < length us" and inactive: "j \<notin> \<mu> (g,length us)"
      and h: "h = us ! j"
      unfolding muterm_frozen_root_on_def by blast
    show ?thesis unfolding muterm_frozen_root_on_def
      by (intro exI[of _ "i # p"] exI[of _ g] exI[of _ us] exI[of _ j],
          use i p at j inactive h in auto)
  qed
qed

inductive muterm_frozen_component_on ::
  "'f mu \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool"
for \<mu>
where
  direct: "muterm_frozen_root_on \<mu> u s \<Longrightarrow>
    muterm_frozen_component_on \<mu> u s"
| nested: "muterm_frozen_root_on \<mu> u h \<Longrightarrow>
    muterm_frozen_component_on \<mu> h s \<Longrightarrow>
    muterm_frozen_component_on \<mu> u s"

definition muterm_active_defined_call_on ::
  "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f,'v) term \<Rightarrow>
    ('f,'v) term \<Rightarrow> bool"
where
  "muterm_active_defined_call_on \<mu> D h t \<longleftrightarrow>
    (\<exists>p. p \<in> mu_fun_poss \<mu> h \<and> h |_ p = t \<and> root t \<in> Some ` D)"

definition muterm_unhiding_safe_on ::
  "'f mu \<Rightarrow> ('f,'v) trs \<Rightarrow> bool"
where
  "muterm_unhiding_safe_on \<mu> R \<longleftrightarrow>
    (\<forall>l r h. (l,r) \<in> R \<longrightarrow> muterm_frozen_root_on \<mu> r h \<longrightarrow>
      is_Fun h \<longrightarrow> mu_vars_term \<mu> h \<subseteq> mu_vars_term \<mu> l) \<and>
    (\<forall>l r x. (l,r) \<in> R \<longrightarrow>
      x \<in> mu_vars_term \<mu> r \<longrightarrow> x \<notin> mu_vars_term \<mu> l \<longrightarrow>
      muterm_frozen_root_on \<mu> l (Var x)) \<and>
    (\<forall>l r x. (l,r) \<in> R \<longrightarrow>
      muterm_frozen_root_on \<mu> r (Var x) \<longrightarrow>
      x \<in> mu_vars_term \<mu> l \<or> muterm_frozen_root_on \<mu> l (Var x)) \<and>
    (\<forall>l r h s. (l,r) \<in> R \<longrightarrow> muterm_frozen_root_on \<mu> r h \<longrightarrow>
      is_Fun h \<longrightarrow> \<not> muterm_frozen_root_on \<mu> h s)"

definition muterm_unhiding_coverage ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> 'f sig \<Rightarrow>
    ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> bool"
where
  "muterm_unhiding_coverage shp \<mu> D R P U \<longleftrightarrow>
    mu_CSDP_on shp \<mu> D R \<subseteq> P \<and>
    csr_rta08_collapsing_CSDP_on shp \<mu> R \<subseteq> P \<and>
    muterm_unhiding_safe_on \<mu> R \<and>
    (\<forall>h t. (\<exists>l r. (l,r) \<in> R \<and> muterm_frozen_root_on \<mu> r h) \<longrightarrow>
      muterm_active_defined_call_on \<mu> D h t \<longrightarrow>
      (h,sharp_term shp t) \<in> U)"

definition is_muterm_unhidable ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow>
    (('f,'v) term \<times> ('f,'v) term) set \<Rightarrow> ('f,'v) trs \<Rightarrow>
    ('f,'v) term \<Rightarrow> bool"
where
  "is_muterm_unhidable shp \<mu> A U u \<longleftrightarrow>
    (\<forall>s t. muterm_frozen_component_on \<mu> u s \<longrightarrow>
      (s = t \<or> mu_supt \<mu> s t) \<longrightarrow> t \<in> mu_Tinf \<mu> A \<longrightarrow>
      (s,sharp_term shp t) \<in> rstep U)"

definition has_muterm_unhiding_property ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow>
    (('f,'v) term \<times> ('f,'v) term) set \<Rightarrow> ('f,'v) trs \<Rightarrow>
    ('f,'v) term \<Rightarrow> bool"
where
  "has_muterm_unhiding_property shp \<mu> A U u \<longleftrightarrow>
    u \<in> mu_Tinf \<mu> A \<and> is_muterm_unhidable shp \<mu> A U u"

lemma muterm_frozen_root_supt:
  assumes frozen: "muterm_frozen_root_on \<mu> u s"
  shows "u \<rhd> s"
proof -
  from frozen obtain p f ts i where p: "p \<in> mu_fun_poss \<mu> u"
    and up: "u |_ p = Fun f ts" and i: "i < length ts" and s: "s = ts ! i"
    unfolding muterm_frozen_root_on_def by blast
  have pposs: "p \<in> poss u"
    using p mu_fun_poss_imp_fun_poss fun_poss_imp_poss by blast
  have iposs: "[i] \<in> poss (u |_ p)" unfolding up using i by simp
  have pi: "p @ [i] \<in> poss u"
    using pposs iposs unfolding poss_append_poss by blast
  have sub: "u |_ (p @ [i]) = s"
    using pposs i up s by (simp add: subt_at_append)
  obtain k qs where shape: "p @ [i] = k # qs" by (cases p, auto)
  show ?thesis
    using subt_at_nepos_imp_supt[OF pi[unfolded shape]] sub shape by simp
qed

lemma muterm_frozen_component_supt:
  assumes "muterm_frozen_component_on \<mu> u s"
  shows "u \<rhd> s"
  using assms
proof induct
  case (direct u s)
  show ?case by (rule muterm_frozen_root_supt[OF direct])
next
  case (nested u h s)
  from muterm_frozen_root_supt[OF nested(1)] nested(3)
  show ?case by (rule supt_trans)
qed

lemma muterm_frozen_component_source_is_Fun:
  assumes "muterm_frozen_component_on \<mu> u s"
  shows "is_Fun u"
  using assms
proof cases
  case direct
  from direct obtain p f ts i where "p \<in> mu_fun_poss \<mu> u"
    unfolding muterm_frozen_root_on_def by blast
  then show ?thesis by (cases u, auto)
next
  case nested
  from nested(1) obtain p f ts i where "p \<in> mu_fun_poss \<mu> u"
    unfolding muterm_frozen_root_on_def by blast
  then show ?thesis by (cases u, auto)
qed

lemma Tinf_has_muterm_unhiding_property:
  assumes T: "u \<in> Tinf A"
  shows "has_muterm_unhiding_property shp \<mu> A U u"
proof -
  have muT: "u \<in> mu_Tinf \<mu> A"
    by (rule Tinf_imp_mu_Tinf[OF T])
  show ?thesis
    unfolding has_muterm_unhiding_property_def is_muterm_unhidable_def
  proof (intro conjI allI impI)
    show "u \<in> mu_Tinf \<mu> A" by (rule muT)
  next
    fix s t
    assume frozen: "muterm_frozen_component_on \<mu> u s"
      and st: "s = t \<or> mu_supt \<mu> s t" and tT: "t \<in> mu_Tinf \<mu> A"
    have us: "u \<rhd> s" by (rule muterm_frozen_component_supt[OF frozen])
    have ut: "u \<rhd> t"
      using us st mu_supt_imp_supt by (meson supt_trans)
    from T ut have "SN_on A {t}" unfolding Tinf_def by auto
    moreover from tT have "\<not> SN_on A {t}" unfolding mu_Tinf_def by auto
    ultimately show "(s,sharp_term shp t) \<in> rstep U" by contradiction
  qed
qed

lemma muterm_unhiding_coverage_mu:
  assumes "muterm_unhiding_coverage shp \<mu> D R P U"
  shows "mu_CSDP_on shp \<mu> D R \<subseteq> P"
  using assms unfolding muterm_unhiding_coverage_def by auto

lemma muterm_unhiding_coverage_collapsing:
  assumes "muterm_unhiding_coverage shp \<mu> D R P U"
  shows "csr_rta08_collapsing_CSDP_on shp \<mu> R \<subseteq> P"
  using assms unfolding muterm_unhiding_coverage_def by auto

lemma muterm_unhiding_coverage_safe:
  assumes "muterm_unhiding_coverage shp \<mu> D R P U"
  shows "muterm_unhiding_safe_on \<mu> R"
  using assms unfolding muterm_unhiding_coverage_def by auto

lemma muterm_unhiding_coverage_rule:
  assumes cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R"
    and frozen: "muterm_frozen_root_on \<mu> r h"
    and call: "muterm_active_defined_call_on \<mu> D h t"
  shows "(h,sharp_term shp t) \<in> U"
  using cover lr frozen call unfolding muterm_unhiding_coverage_def by blast

lemma muterm_unhiding_safe_vars:
  assumes cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R"
    and frozen: "muterm_frozen_root_on \<mu> r h"
    and hfun: "is_Fun h"
    and x: "x \<in> mu_vars_term \<mu> h"
  shows "x \<in> mu_vars_term \<mu> l"
  using muterm_unhiding_coverage_safe[OF cover] lr frozen hfun x
  unfolding muterm_unhiding_safe_on_def by blast

lemma muterm_unhiding_safe_migrating:
  assumes cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R" and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
  shows "muterm_frozen_root_on \<mu> l (Var x)"
proof -
  from muterm_unhiding_coverage_safe[OF cover]
  have migrating: "\<forall>l r x. (l,r) \<in> R \<longrightarrow>
      x \<in> mu_vars_term \<mu> r \<longrightarrow> x \<notin> mu_vars_term \<mu> l \<longrightarrow>
      muterm_frozen_root_on \<mu> l (Var x)"
    unfolding muterm_unhiding_safe_on_def by (elim conjE)
  show ?thesis by (rule migrating[rule_format, OF lr xr xl])
qed

lemma muterm_unhiding_safe_frozen_var:
  assumes cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R" and frozen: "muterm_frozen_root_on \<mu> r (Var x)"
  shows "x \<in> mu_vars_term \<mu> l \<or> muterm_frozen_root_on \<mu> l (Var x)"
  using muterm_unhiding_coverage_safe[OF cover] lr frozen
  unfolding muterm_unhiding_safe_on_def by blast

lemma muterm_unhiding_safe_flat:
  assumes cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R" and frozen: "muterm_frozen_root_on \<mu> r h"
    and hfun: "is_Fun h"
  shows "\<not> muterm_frozen_root_on \<mu> h s"
  using muterm_unhiding_coverage_safe[OF cover] lr frozen hfun
  unfolding muterm_unhiding_safe_on_def by blast

lemma mu_fun_poss_compose:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
    and q: "q \<in> mu_fun_poss \<mu> (t |_ p)"
  shows "p @ q \<in> mu_fun_poss \<mu> t"
  using p q
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from Cons.prems have i: "i < length ts" "i \<in> \<mu> (f,length ts)"
    and p: "p \<in> mu_fun_poss \<mu> (ts ! i)"
    and q: "q \<in> mu_fun_poss \<mu> ((ts ! i) |_ p)"
    unfolding t by auto
  from Cons.hyps[OF p q] have "p @ q \<in> mu_fun_poss \<mu> (ts ! i)" .
  with i show ?case unfolding t by simp
qed

lemma muterm_frozen_root_active_subterm:
  assumes active: "v = u \<or> mu_supt \<mu> v u"
    and frozen: "muterm_frozen_root_on \<mu> u s"
  shows "muterm_frozen_root_on \<mu> v s"
proof (rule disjE[OF active])
  assume "v = u"
  then show ?thesis using frozen by simp
next
  assume "mu_supt \<mu> v u"
  then obtain i q where iq: "i # q \<in> mu_poss \<mu> v"
    and sub: "v |_ (i # q) = u"
    unfolding mu_supt_def by blast
  from frozen obtain p f ts j where p: "p \<in> mu_fun_poss \<mu> u"
    and up: "u |_ p = Fun f ts" and j: "j < length ts"
    and inactive: "j \<notin> \<mu> (f,length ts)" and s: "s = ts ! j"
    unfolding muterm_frozen_root_on_def by blast
  have base_fun: "i # q \<in> mu_fun_poss \<mu> v"
  proof -
    have ufun: "is_Fun u" using p by (cases u, auto)
    have fpos: "i # q \<in> fun_poss v"
      by (rule poss_is_Fun_fun_poss[OF mu_poss_imp_poss[OF iq]],
          use sub ufun in simp)
    show ?thesis by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF iq fpos])
  qed
  have comp: "(i # q) @ p \<in> mu_fun_poss \<mu> v"
    by (rule mu_fun_poss_compose[OF base_fun], use p sub in simp)
  have subat: "v |_ ((i # q) @ p) = Fun f ts"
  proof -
    have "v |_ ((i # q) @ p) = (v |_ (i # q)) |_ p"
      by (rule subt_at_append[OF mu_poss_imp_poss[OF iq]])
    also have "... = Fun f ts" using sub up by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding muterm_frozen_root_on_def
    by (intro exI[of _ "(i # q) @ p"] exI[of _ f] exI[of _ ts]
        exI[of _ j], use comp subat j inactive s in auto)
qed

lemma muterm_frozen_component_active_subterm:
  assumes active: "v = u \<or> mu_supt \<mu> v u"
    and component: "muterm_frozen_component_on \<mu> u s"
  shows "muterm_frozen_component_on \<mu> v s"
  using component
proof cases
  case direct
  show ?thesis by (rule muterm_frozen_component_on.direct,
      rule muterm_frozen_root_active_subterm[OF active direct])
next
  case (nested h)
  have vh: "muterm_frozen_root_on \<mu> v h"
    by (rule muterm_frozen_root_active_subterm[OF active nested(1)])
  show ?thesis by (rule muterm_frozen_component_on.nested[OF vh nested(2)])
qed

lemma muterm_frozen_component_on_Fun:
  "muterm_frozen_component_on \<mu> (Fun f ts) s \<longleftrightarrow>
    (\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_frozen_component_on \<mu> (ts ! i) s) \<or>
    (\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and>
      (s = ts ! i \<or> muterm_frozen_component_on \<mu> (ts ! i) s))"
proof
  assume comp: "muterm_frozen_component_on \<mu> (Fun f ts) s"
  from comp show "(\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_frozen_component_on \<mu> (ts ! i) s) \<or>
    (\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and>
      (s = ts ! i \<or> muterm_frozen_component_on \<mu> (ts ! i) s))"
  proof cases
    case direct
    from direct[unfolded muterm_frozen_root_on_Fun]
    show ?thesis by (blast intro: muterm_frozen_component_on.direct)
  next
    case (nested h)
    from nested(1)[unfolded muterm_frozen_root_on_Fun]
    show ?thesis
    proof
      assume "\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and> h = ts ! i"
      with nested(2) show ?thesis by blast
    next
      assume "\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
        muterm_frozen_root_on \<mu> (ts ! i) h"
      then obtain i where i: "i < length ts" "i \<in> \<mu> (f,length ts)"
        and root: "muterm_frozen_root_on \<mu> (ts ! i) h" by blast
      have "muterm_frozen_component_on \<mu> (ts ! i) s"
        by (rule muterm_frozen_component_on.nested[OF root nested(2)])
      with i show ?thesis by blast
    qed
  qed
next
  assume split: "(\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_frozen_component_on \<mu> (ts ! i) s) \<or>
    (\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and>
      (s = ts ! i \<or> muterm_frozen_component_on \<mu> (ts ! i) s))"
  show "muterm_frozen_component_on \<mu> (Fun f ts) s"
  proof (rule disjE[OF split])
    assume "\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_frozen_component_on \<mu> (ts ! i) s"
    then obtain i where i: "i < length ts" "i \<in> \<mu> (f,length ts)"
      and comp: "muterm_frozen_component_on \<mu> (ts ! i) s" by blast
    have child_fun: "is_Fun (ts ! i)"
      by (rule muterm_frozen_component_source_is_Fun[OF comp])
    have active: "mu_supt \<mu> (Fun f ts) (ts ! i)"
      unfolding mu_supt_def using i child_fun
      by (intro exI[of _ i] exI[of _ "[]"], cases "ts ! i", auto)
    show ?thesis by (rule muterm_frozen_component_active_subterm[
      OF disjI2[OF active] comp])
  next
    assume "\<exists>i<length ts. i \<notin> \<mu> (f,length ts) \<and>
      (s = ts ! i \<or> muterm_frozen_component_on \<mu> (ts ! i) s)"
    then obtain i where i: "i < length ts" "i \<notin> \<mu> (f,length ts)"
      and rest: "s = ts ! i \<or> muterm_frozen_component_on \<mu> (ts ! i) s" by blast
    have root: "muterm_frozen_root_on \<mu> (Fun f ts) (ts ! i)"
      unfolding muterm_frozen_root_on_Fun using i by blast
    show ?thesis
    proof (rule disjE[OF rest])
      assume eq: "s = ts ! i"
      have "muterm_frozen_component_on \<mu> (Fun f ts) (ts ! i)"
        by (rule muterm_frozen_component_on.direct[OF root])
      then show ?thesis unfolding eq .
    next
      assume comp: "muterm_frozen_component_on \<mu> (ts ! i) s"
      show ?thesis by (rule muterm_frozen_component_on.nested[OF root comp])
    qed
  qed
qed

lemma muterm_unhidable_active_subterm:
  assumes unhidable: "is_muterm_unhidable shp \<mu> A U v"
    and active: "v = u \<or> mu_supt \<mu> v u"
  shows "is_muterm_unhidable shp \<mu> A U u"
  unfolding is_muterm_unhidable_def
proof (intro allI impI)
  fix s t
  assume frozen: "muterm_frozen_component_on \<mu> u s"
    and st: "s = t \<or> mu_supt \<mu> s t" and tT: "t \<in> mu_Tinf \<mu> A"
  have frozen_v: "muterm_frozen_component_on \<mu> v s"
  proof -
    have split: "muterm_frozen_root_on \<mu> u s \<or>
      (\<exists>h. muterm_frozen_root_on \<mu> u h \<and>
        muterm_frozen_component_on \<mu> h s)"
      using frozen by (cases, auto)
    show ?thesis
    proof (rule disjE[OF split])
      assume us: "muterm_frozen_root_on \<mu> u s"
      show ?thesis by (rule muterm_frozen_component_on.direct,
          rule muterm_frozen_root_active_subterm[OF active us])
    next
      assume "\<exists>h. muterm_frozen_root_on \<mu> u h \<and>
        muterm_frozen_component_on \<mu> h s"
      then obtain h where uh: "muterm_frozen_root_on \<mu> u h"
        and hs: "muterm_frozen_component_on \<mu> h s" by blast
      have vh: "muterm_frozen_root_on \<mu> v h"
        by (rule muterm_frozen_root_active_subterm[OF active uh])
      show ?thesis by (rule muterm_frozen_component_on.nested[OF vh hs])
    qed
  qed
  from unhidable frozen_v st tT show "(s,sharp_term shp t) \<in> rstep U"
    unfolding is_muterm_unhidable_def by blast
qed

lemma muterm_frozen_root_subst:
  assumes frozen: "muterm_frozen_root_on \<mu> l h"
  shows "muterm_frozen_root_on \<mu> (l \<cdot> \<sigma>) (h \<cdot> \<sigma>)"
proof -
  from frozen obtain p f ts i where p: "p \<in> mu_fun_poss \<mu> l"
    and lp: "l |_ p = Fun f ts" and i: "i < length ts"
    and inactive: "i \<notin> \<mu> (f,length ts)" and h: "h = ts ! i"
    unfolding muterm_frozen_root_on_def by blast
  have psub: "p \<in> mu_fun_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_subst_lift[OF p])
  have pposs: "p \<in> poss l"
    using p mu_fun_poss_imp_fun_poss fun_poss_imp_poss by blast
  have at: "(l \<cdot> \<sigma>) |_ p = Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
    using subt_at_subst[OF pposs, of \<sigma>] lp by simp
  have len: "i < length (map (\<lambda>t. t \<cdot> \<sigma>) ts)" using i by simp
  have nth: "h \<cdot> \<sigma> = map (\<lambda>t. t \<cdot> \<sigma>) ts ! i"
    using h i by simp
  show ?thesis unfolding muterm_frozen_root_on_def
    by (intro exI[of _ p] exI[of _ f]
        exI[of _ "map (\<lambda>t. t \<cdot> \<sigma>) ts"] exI[of _ i],
        use psub at len inactive nth in auto)
qed

lemma muterm_frozen_root_subst_cases:
  assumes frozen: "muterm_frozen_root_on \<mu> (r \<cdot> \<sigma>) s"
  obtains
    (source_fun) h where "muterm_frozen_root_on \<mu> r h" "is_Fun h" "s = h \<cdot> \<sigma>"
  | (source_var) x where "muterm_frozen_root_on \<mu> r (Var x)" "s = \<sigma> x"
  | (in_subst) x where "x \<in> mu_vars_term \<mu> r"
      "muterm_frozen_root_on \<mu> (\<sigma> x) s"
  using frozen
proof (induct r arbitrary: s)
  case (Var x)
  have x: "x \<in> mu_vars_term \<mu> (Var x)"
    unfolding mu_vars_term_def by auto
  show ?case
  proof (rule Var(3)[OF x])
    show "muterm_frozen_root_on \<mu> (\<sigma> x) s"
      using Var.prems by simp
  qed
next
  case (Fun f rs)
  note emit_source_fun = Fun(2)
  note emit_source_var = Fun(3)
  note emit_in_subst = Fun(4)
  from Fun.prems obtain p g ts i where p: "p \<in> mu_fun_poss \<mu> (Fun f rs \<cdot> \<sigma>)"
    and at: "(Fun f rs \<cdot> \<sigma>) |_ p = Fun g ts"
    and i: "i < length ts" and inactive: "i \<notin> \<mu> (g,length ts)"
    and s: "s = ts ! i"
    unfolding muterm_frozen_root_on_def by blast
  show ?case
  proof (cases p)
    case Nil
    from at Nil have g: "g = f" and ts: "ts = map (\<lambda>t. t \<cdot> \<sigma>) rs"
      by auto
    from i ts obtain ri where ri: "ri = rs ! i" and ilen: "i < length rs"
      by auto
    have source_frozen: "muterm_frozen_root_on \<mu> (Fun f rs) ri"
      unfolding muterm_frozen_root_on_def
      by (intro exI[of _ "[]"] exI[of _ f] exI[of _ rs] exI[of _ i],
          use ilen inactive g ts ri in auto)
    have s_inst: "s = ri \<cdot> \<sigma>" using s ts ri i by simp
    show ?thesis
    proof (cases ri)
      case (Var x)
      have sx: "s = \<sigma> x" using s_inst Var by simp
      from emit_source_var[OF source_frozen[unfolded Var] sx]
      show ?thesis .
    next
      case (Fun h hs)
      have "is_Fun ri" unfolding Fun by simp
      from emit_source_fun[OF source_frozen this s_inst]
      show ?thesis .
    qed
  next
    case (Cons j q)
    from p Cons have j: "j < length rs" "j \<in> \<mu> (f,length rs)"
      and q: "q \<in> mu_fun_poss \<mu> (rs ! j \<cdot> \<sigma>)"
      by auto
    have subeq: "(rs ! j \<cdot> \<sigma>) |_ q = Fun g ts"
      using at Cons j by simp
    have frozen_arg: "muterm_frozen_root_on \<mu> (rs ! j \<cdot> \<sigma>) s"
      unfolding muterm_frozen_root_on_def
      by (intro exI[of _ q] exI[of _ g] exI[of _ ts] exI[of _ i],
          use q subeq i inactive s in auto)
    show ?thesis
    proof (rule Fun.hyps)
      show "rs ! j \<in> set rs" by (rule nth_mem[OF j(1)])
    next
      fix h
      assume source_fun1: "muterm_frozen_root_on \<mu> (rs ! j) h"
        and source_fun2: "is_Fun h" and source_fun3: "s = h \<cdot> \<sigma>"
      have whole: "muterm_frozen_root_on \<mu> (Fun f rs) h"
      proof -
        from source_fun1 obtain p' k us m where p': "p' \<in> mu_fun_poss \<mu> (rs ! j)"
          and at': "rs ! j |_ p' = Fun k us" and m: "m < length us"
          and mi: "m \<notin> \<mu> (k,length us)" and h: "h = us ! m"
          unfolding muterm_frozen_root_on_def by blast
        show ?thesis unfolding muterm_frozen_root_on_def
          by (intro exI[of _ "j # p'"] exI[of _ k] exI[of _ us] exI[of _ m],
              use j p' at' m mi h in auto)
      qed
      from emit_source_fun[OF whole source_fun2 source_fun3] show ?thesis .
    next
      fix x
      assume source_var1: "muterm_frozen_root_on \<mu> (rs ! j) (Var x)"
        and source_var2: "s = \<sigma> x"
      have whole: "muterm_frozen_root_on \<mu> (Fun f rs) (Var x)"
      proof -
        from source_var1 obtain p' k us m where p': "p' \<in> mu_fun_poss \<mu> (rs ! j)"
          and at': "rs ! j |_ p' = Fun k us" and m: "m < length us"
          and mi: "m \<notin> \<mu> (k,length us)" and x: "Var x = us ! m"
          unfolding muterm_frozen_root_on_def by blast
        show ?thesis unfolding muterm_frozen_root_on_def
          by (intro exI[of _ "j # p'"] exI[of _ k] exI[of _ us] exI[of _ m],
              use j p' at' m mi x in auto)
      qed
      from emit_source_var[OF whole source_var2] show ?thesis .
    next
      fix x
      assume in_subst1: "x \<in> mu_vars_term \<mu> (rs ! j)"
        and in_subst2: "muterm_frozen_root_on \<mu> (\<sigma> x) s"
      have xwhole: "x \<in> mu_vars_term \<mu> (Fun f rs)"
      proof -
        from in_subst1 obtain p' where p': "p' \<in> mu_poss \<mu> (rs ! j)"
          and xp: "rs ! j |_ p' = Var x"
          unfolding mu_vars_term_def by blast
        have "j # p' \<in> mu_poss \<mu> (Fun f rs)" using j p' by auto
        moreover have "Fun f rs |_ (j # p') = Var x" using j xp by simp
        ultimately show ?thesis unfolding mu_vars_term_def by blast
      qed
      from emit_in_subst[OF xwhole in_subst2] show ?thesis .
    next
      show "muterm_frozen_root_on \<mu> (rs ! j \<cdot> \<sigma>) s"
        by (rule frozen_arg)
    qed
  qed
qed

lemma muterm_flat_component_subst:
  assumes flat: "\<And>h. \<not> muterm_frozen_root_on \<mu> r h"
    and component: "muterm_frozen_component_on \<mu> (r \<cdot> \<sigma>) s"
  obtains x where "x \<in> mu_vars_term \<mu> r"
    "muterm_frozen_component_on \<mu> (\<sigma> x) s"
  using component
proof cases
  case direct
  from direct show thesis
  proof (elim muterm_frozen_root_subst_cases)
    fix h
    assume root: "muterm_frozen_root_on \<mu> r h" and "is_Fun h" and "s = h \<cdot> \<sigma>"
    from flat[of h] root show thesis by contradiction
  next
    fix x
    assume root: "muterm_frozen_root_on \<mu> r (Var x)" and "s = \<sigma> x"
    from flat[of "Var x"] root show thesis by contradiction
  next
    fix x
    assume in_subst1: "x \<in> mu_vars_term \<mu> r"
      and in_subst2: "muterm_frozen_root_on \<mu> (\<sigma> x) s"
    have comp: "muterm_frozen_component_on \<mu> (\<sigma> x) s"
      by (rule muterm_frozen_component_on.direct[OF in_subst2])
    show thesis by (rule that[OF in_subst1 comp])
  qed
next
  case (nested h)
  from nested(1) show thesis
  proof (elim muterm_frozen_root_subst_cases)
    fix h0
    assume root: "muterm_frozen_root_on \<mu> r h0" and "is_Fun h0"
      and "h = h0 \<cdot> \<sigma>"
    from flat[of h0] root show thesis by contradiction
  next
    fix x
    assume root: "muterm_frozen_root_on \<mu> r (Var x)" and "h = \<sigma> x"
    from flat[of "Var x"] root show thesis by contradiction
  next
    fix x
    assume in_subst1: "x \<in> mu_vars_term \<mu> r"
      and in_subst2: "muterm_frozen_root_on \<mu> (\<sigma> x) h"
    have comp: "muterm_frozen_component_on \<mu> (\<sigma> x) s"
      by (rule muterm_frozen_component_on.nested[OF in_subst2 nested(2)])
    show thesis by (rule that[OF in_subst1 comp])
  qed
qed

lemma muterm_rhs_component_cases:
  assumes cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R" and lhs: "is_Fun l"
    and component: "muterm_frozen_component_on \<mu> (r \<cdot> \<sigma>) s"
  obtains
    (new_fun) h where "muterm_frozen_root_on \<mu> r h" "is_Fun h"
      "s = h \<cdot> \<sigma>"
  | (inherited) "muterm_frozen_component_on \<mu> (l \<cdot> \<sigma>) s"
  | (active_var) x where "x \<in> mu_vars_term \<mu> l" "s = \<sigma> x"
proof -
  have lift_active: "\<And>x z. x \<in> mu_vars_term \<mu> l \<Longrightarrow>
      muterm_frozen_component_on \<mu> (\<sigma> x) z \<Longrightarrow>
      muterm_frozen_component_on \<mu> (l \<cdot> \<sigma>) z"
  proof -
    fix x z
    assume x: "x \<in> mu_vars_term \<mu> l"
      and comp: "muterm_frozen_component_on \<mu> (\<sigma> x) z"
    have active: "mu_supt \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
      by (rule mu_vars_term_subst_mu_supt[OF lhs x])
    show "muterm_frozen_component_on \<mu> (l \<cdot> \<sigma>) z"
      by (rule muterm_frozen_component_active_subterm[OF disjI2[OF active] comp])
  qed
  have lift_frozen: "\<And>x z. muterm_frozen_root_on \<mu> l (Var x) \<Longrightarrow>
      muterm_frozen_component_on \<mu> (\<sigma> x) z \<Longrightarrow>
      muterm_frozen_component_on \<mu> (l \<cdot> \<sigma>) z"
  proof -
    fix x z
    assume x: "muterm_frozen_root_on \<mu> l (Var x)"
      and comp: "muterm_frozen_component_on \<mu> (\<sigma> x) z"
    have root: "muterm_frozen_root_on \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
      using muterm_frozen_root_subst[OF x, of \<sigma>] by simp
    show "muterm_frozen_component_on \<mu> (l \<cdot> \<sigma>) z"
      by (rule muterm_frozen_component_on.nested[OF root comp])
  qed
  from component show thesis
  proof cases
    case direct
    from direct show thesis
    proof (elim muterm_frozen_root_subst_cases)
      fix h
      assume root: "muterm_frozen_root_on \<mu> r h" and hfun: "is_Fun h"
        and s: "s = h \<cdot> \<sigma>"
      show thesis by (rule new_fun[OF root hfun s])
    next
      fix x
      assume root_r: "muterm_frozen_root_on \<mu> r (Var x)" and s: "s = \<sigma> x"
      from muterm_unhiding_safe_frozen_var[OF cover lr root_r]
      show thesis
      proof
        assume x: "x \<in> mu_vars_term \<mu> l"
        show thesis by (rule active_var[OF x s])
      next
        assume x: "muterm_frozen_root_on \<mu> l (Var x)"
        have root: "muterm_frozen_root_on \<mu> (l \<cdot> \<sigma>) s"
          using muterm_frozen_root_subst[OF x, of \<sigma>] s by simp
        show thesis by (rule inherited,
            rule muterm_frozen_component_on.direct[OF root])
      qed
    next
      fix x
      assume in_subst1: "x \<in> mu_vars_term \<mu> r"
        and in_subst2: "muterm_frozen_root_on \<mu> (\<sigma> x) s"
      have comp: "muterm_frozen_component_on \<mu> (\<sigma> x) s"
        by (rule muterm_frozen_component_on.direct[OF in_subst2])
      show thesis
      proof (cases "x \<in> mu_vars_term \<mu> l")
        case True
        show thesis by (rule inherited, rule lift_active[OF True comp])
      next
        case False
        have frozen_l: "muterm_frozen_root_on \<mu> l (Var x)"
          by (rule muterm_unhiding_safe_migrating[OF cover lr in_subst1 False])
        show thesis by (rule inherited, rule lift_frozen[OF frozen_l comp])
      qed
    qed
  next
    case (nested h)
    from nested(1) show thesis
    proof (elim muterm_frozen_root_subst_cases)
      fix h0
      assume source_fun1: "muterm_frozen_root_on \<mu> r h0"
        and source_fun2: "is_Fun h0" and source_fun3: "h = h0 \<cdot> \<sigma>"
      have flat: "\<And>z. \<not> muterm_frozen_root_on \<mu> h0 z"
        by (rule muterm_unhiding_safe_flat[OF cover lr source_fun1 source_fun2])
      have comp_h0: "muterm_frozen_component_on \<mu> (h0 \<cdot> \<sigma>) s"
        using nested(2) source_fun3 by simp
      from muterm_flat_component_subst[OF flat comp_h0]
      obtain x where xh: "x \<in> mu_vars_term \<mu> h0"
        and comp: "muterm_frozen_component_on \<mu> (\<sigma> x) s" .
      have xl: "x \<in> mu_vars_term \<mu> l"
        by (rule muterm_unhiding_safe_vars[OF cover lr source_fun1 source_fun2 xh])
      show thesis by (rule inherited, rule lift_active[OF xl comp])
    next
      fix x
      assume source_var1: "muterm_frozen_root_on \<mu> r (Var x)"
        and source_var2: "h = \<sigma> x"
      have comp: "muterm_frozen_component_on \<mu> (\<sigma> x) s"
        using nested(2) source_var2 by simp
      from muterm_unhiding_safe_frozen_var[OF cover lr source_var1]
      show thesis
      proof
        assume xl: "x \<in> mu_vars_term \<mu> l"
        show thesis by (rule inherited, rule lift_active[OF xl comp])
      next
        assume frozen_l: "muterm_frozen_root_on \<mu> l (Var x)"
        show thesis by (rule inherited, rule lift_frozen[OF frozen_l comp])
      qed
    next
      fix x
      assume in_subst1: "x \<in> mu_vars_term \<mu> r"
        and in_subst2: "muterm_frozen_root_on \<mu> (\<sigma> x) h"
      have comp: "muterm_frozen_component_on \<mu> (\<sigma> x) s"
        by (rule muterm_frozen_component_on.nested[OF in_subst2 nested(2)])
      show thesis
      proof (cases "x \<in> mu_vars_term \<mu> l")
        case True
        show thesis by (rule inherited, rule lift_active[OF True comp])
      next
        case False
        have frozen_l: "muterm_frozen_root_on \<mu> l (Var x)"
          by (rule muterm_unhiding_safe_migrating[OF cover lr in_subst1 False])
        show thesis by (rule inherited, rule lift_frozen[OF frozen_l comp])
      qed
    qed
  qed
qed

lemma muterm_new_frozen_fun_unhide_finite:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R" and lhs: "is_Fun l"
    and source_finite: "\<And>x q. x \<in> mu_vars_term \<mu> l \<Longrightarrow>
      q \<in> mu_fun_poss \<mu> (\<sigma> x) \<Longrightarrow>
      SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
    and frozen: "muterm_frozen_root_on \<mu> r h" and hfun: "is_Fun h"
    and active: "h \<cdot> \<sigma> = t \<or> mu_supt \<mu> (h \<cdot> \<sigma>) t"
    and tT: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "(h \<cdot> \<sigma>,sharp_term shp t) \<in> rstep U"
proof -
  from mu_Tinf_defined_root[OF wf tT]
  obtain f ts where tfun: "t = Fun f ts" and tdef: "defined R (f,length ts)" .
  have t_isfun: "is_Fun t" unfolding tfun by simp
  obtain p where p: "p \<in> mu_fun_poss \<mu> (h \<cdot> \<sigma>)"
    and hp: "(h \<cdot> \<sigma>) |_ p = t"
  proof (rule disjE[OF active])
    assume eq: "h \<cdot> \<sigma> = t"
    have "[] \<in> mu_fun_poss \<mu> (h \<cdot> \<sigma>)"
      using hfun by (cases h, auto)
    moreover have "(h \<cdot> \<sigma>) |_ [] = t" using eq by simp
    ultimately show thesis by (rule that)
  next
    assume sub: "mu_supt \<mu> (h \<cdot> \<sigma>) t"
    then obtain i q where iq: "i # q \<in> mu_poss \<mu> (h \<cdot> \<sigma>)"
      and at: "(h \<cdot> \<sigma>) |_ (i # q) = t"
      unfolding mu_supt_def by blast
    have fp: "i # q \<in> fun_poss (h \<cdot> \<sigma>)"
      by (rule poss_is_Fun_fun_poss[OF mu_poss_imp_poss[OF iq]],
          use at t_isfun in simp)
    have mp: "i # q \<in> mu_fun_poss \<mu> (h \<cdot> \<sigma>)"
      by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF iq fp])
    show thesis by (rule that[OF mp at])
  qed
  from mu_fun_poss_subst_cases_aux_mu[OF p]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> h \<and>
      (h \<cdot> \<sigma>) |_ p = (h |_ p) \<cdot> \<sigma>"
    then have ph: "p \<in> mu_fun_poss \<mu> h"
      and inst: "t = (h |_ p) \<cdot> \<sigma>" using hp by auto
    from ph obtain g us where base: "h |_ p = Fun g us"
      using mu_fun_poss_imp_fun_poss fun_poss_fun_conv by blast
    from inst tfun base have gf: "g = f" and len: "length us = length ts" by auto
    have rootD: "root (h |_ p) \<in> Some ` D"
      unfolding base using defs tdef gf len by auto
    have call: "muterm_active_defined_call_on \<mu> D h (h |_ p)"
      unfolding muterm_active_defined_call_on_def using ph rootD by blast
    have rule: "(h,sharp_term shp (h |_ p)) \<in> U"
      by (rule muterm_unhiding_coverage_rule[OF cover lr frozen call])
    show ?thesis
    proof (rule rstepI[OF rule, where C=\<box> and \<sigma>=\<sigma>])
      show "h \<cdot> \<sigma> = \<box>\<langle>h \<cdot> \<sigma>\<rangle>" by simp
      have subfun: "is_Fun (h |_ p)" unfolding base by simp
      show "sharp_term shp t = \<box>\<langle>sharp_term shp (h |_ p) \<cdot> \<sigma>\<rangle>"
        unfolding inst sharp_term_subst_distr_2[OF subfun] by simp
    qed
  next
    assume subst: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> h \<and> h |_ q1 = Var x \<and>
      x \<in> vars_term h \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and>
      (h \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q2 where xh: "x \<in> mu_vars_term \<mu> h"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and ti: "t = \<sigma> x |_ q2"
      unfolding mu_vars_term_def using hp by blast
    have xl: "x \<in> mu_vars_term \<mu> l"
      by (rule muterm_unhiding_safe_vars[OF cover lr frozen hfun xh])
    have sn: "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
      by (rule source_finite[OF xl q2])
    moreover from tT have "\<not> SN_on (csstep \<mu> R) {t}"
      unfolding mu_Tinf_def by auto
    ultimately show ?thesis unfolding ti by contradiction
  qed
qed

lemma muterm_new_frozen_fun_unhide:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R" and lhs: "is_Fun l"
    and source: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and frozen: "muterm_frozen_root_on \<mu> r h" and hfun: "is_Fun h"
    and active: "h \<cdot> \<sigma> = t \<or> mu_supt \<mu> (h \<cdot> \<sigma>) t"
    and tT: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "(h \<cdot> \<sigma>,sharp_term shp t) \<in> rstep U"
  by (rule muterm_new_frozen_fun_unhide_finite[
      OF wf defs cover lr lhs _ frozen hfun active tT],
      rule mu_Tinf_SN_on_active_subst_mu_subterm[OF lhs source])

lemma csrstep_muterm_unhiding_preserve_finite:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and step: "(u,v) \<in> csrstep \<mu> R"
    and source_finite: "\<And>x q l r \<sigma>. (l,r) \<in> R \<Longrightarrow>
      u = l \<cdot> \<sigma> \<Longrightarrow> x \<in> mu_vars_term \<mu> l \<Longrightarrow>
      q \<in> mu_fun_poss \<mu> (\<sigma> x) \<Longrightarrow>
      SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
    and unhidable: "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U u"
  shows "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U v"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and u: "u = l \<cdot> \<sigma>" and v: "v = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l" unfolding wf_trs_def by (cases l, auto)
  show ?thesis unfolding is_muterm_unhidable_def
  proof (intro allI impI)
    fix s t
    assume component: "muterm_frozen_component_on \<mu> v s"
      and active: "s = t \<or> mu_supt \<mu> s t"
      and tT: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    show "(s,sharp_term shp t) \<in> rstep U"
    apply (rule muterm_rhs_component_cases[
      OF cover lr lhs component[unfolded v]])
    proof -
      fix h
      assume new1: "muterm_frozen_root_on \<mu> r h" and new2: "is_Fun h"
        and new3: "s = h \<cdot> \<sigma>"
      show ?thesis unfolding new3
        by (rule muterm_new_frozen_fun_unhide_finite[
          OF wf defs cover lr lhs _ new1 new2 _ tT],
          use source_finite lr u in blast,
          use active new3 in simp)
    next
      assume inherited: "muterm_frozen_component_on \<mu> (l \<cdot> \<sigma>) s"
      from unhidable inherited active tT show ?thesis
        unfolding u is_muterm_unhidable_def by blast
    next
      fix x
      assume active_var1: "x \<in> mu_vars_term \<mu> l" and active_var2: "s = \<sigma> x"
      from mu_Tinf_defined_root[OF wf tT]
      obtain f ts where tfun: "t = Fun f ts" .
      have t_isfun: "is_Fun t" unfolding tfun by simp
      obtain q where q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
        and at: "\<sigma> x |_ q = t"
      proof (rule disjE[OF active])
        assume eq: "s = t"
        have "[] \<in> mu_fun_poss \<mu> (\<sigma> x)"
          using eq active_var2 t_isfun by (cases "\<sigma> x", auto)
        moreover have "\<sigma> x |_ [] = t" using eq active_var2 by simp
        ultimately show thesis by (rule that)
      next
        assume sub: "mu_supt \<mu> s t"
        then obtain i qs where pos: "i # qs \<in> mu_poss \<mu> s"
          and sat: "s |_ (i # qs) = t" unfolding mu_supt_def by blast
        have fp: "i # qs \<in> fun_poss s"
          by (rule poss_is_Fun_fun_poss[OF mu_poss_imp_poss[OF pos]],
              use sat t_isfun in simp)
        have mp: "i # qs \<in> mu_fun_poss \<mu> s"
          by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF pos fp])
        have q': "i # qs \<in> mu_fun_poss \<mu> (\<sigma> x)"
          using mp active_var2 by simp
        have at': "\<sigma> x |_ (i # qs) = t"
          using sat active_var2 by simp
        show thesis by (rule that[OF q' at'])
      qed
      have sn: "SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
        by (rule source_finite[OF lr u active_var1 q])
      moreover from tT have "\<not> SN_on (csstep \<mu> R) {t}"
        unfolding mu_Tinf_def by auto
      ultimately show ?thesis unfolding at by contradiction
    qed
  qed
qed

lemma SN_on_active_subst_mu_subterm:
  assumes wf: "wf_trs R" and lhs: "is_Fun l"
    and source: "SN_on (csstep \<mu> R) {l \<cdot> \<sigma>}"
    and x: "x \<in> mu_vars_term \<mu> l"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
proof -
  from x obtain p where p: "p \<in> mu_poss \<mu> l" and lp: "l |_ p = Var x"
    unfolding mu_vars_term_def by auto
  have pq: "p @ q \<in> mu_fun_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_subst_var_lift[
      where t=l and x=x and \<sigma>=\<sigma>, OF p lp q])
  have sub: "(l \<cdot> \<sigma>) |_ (p @ q) = \<sigma> x |_ q"
    using mu_poss_imp_poss[OF p] lp by (simp add: subt_at_append)
  from SN_on_mu_subterm[OF wf pq source]
  show ?thesis unfolding sub .
qed

lemma csstep_muterm_unhiding_preserve_guarded:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and step: "(u,v) \<in> csstep \<mu> R"
    and guard: "u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<or>
      SN_on (csstep \<mu> R) {u}"
    and unhidable: "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U u"
  shows "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U v"
  using step guard unhidable
proof (induct u arbitrary: v)
  case (Var x)
  from csstep_Var_empty_wf[OF wf, of x v \<mu>] Var.prems(1)
  show ?case by contradiction
next
  case (Fun f ss)
  show ?case
  proof (cases "(Fun f ss,v) \<in> csrstep \<mu> R")
    case True
    have finite: "\<And>x q l r \<sigma>. (l,r) \<in> R \<Longrightarrow>
      Fun f ss = l \<cdot> \<sigma> \<Longrightarrow> x \<in> mu_vars_term \<mu> l \<Longrightarrow>
      q \<in> mu_fun_poss \<mu> (\<sigma> x) \<Longrightarrow>
      SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
    proof -
      fix x q l r \<sigma>
      assume lr: "(l,r) \<in> R" and src: "Fun f ss = l \<cdot> \<sigma>"
        and x: "x \<in> mu_vars_term \<mu> l"
        and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
      from wf lr have lhs: "is_Fun l" unfolding wf_trs_def by (cases l, auto)
      show "SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
      proof (rule disjE[OF Fun.prems(2)])
        assume T: "Fun f ss \<in> mu_Tinf \<mu> (csstep \<mu> R)"
        show ?thesis by (rule mu_Tinf_SN_on_active_subst_mu_subterm[
          OF lhs T[unfolded src] x q])
      next
        assume SN: "SN_on (csstep \<mu> R) {Fun f ss}"
        show ?thesis by (rule SN_on_active_subst_mu_subterm[
          OF wf lhs SN[unfolded src] x q])
      qed
    qed
    show ?thesis
    proof (rule csrstep_muterm_unhiding_preserve_finite[
        where shp=shp and \<mu>=\<mu> and D=D and R=R and P=P and U=U
          and u="Fun f ss" and v=v])
      show "wf_trs R" by (rule wf)
      show "{f. defined R f} \<subseteq> D" by (rule defs)
      show "muterm_unhiding_coverage shp \<mu> D R P U" by (rule cover)
      show "(Fun f ss,v) \<in> csrstep \<mu> R" by (rule True)
      show "\<And>x q l r \<sigma>. (l,r) \<in> R \<Longrightarrow>
          Fun f ss = l \<cdot> \<sigma> \<Longrightarrow> x \<in> mu_vars_term \<mu> l \<Longrightarrow>
          q \<in> mu_fun_poss \<mu> (\<sigma> x) \<Longrightarrow>
          SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
        by (rule finite)
      show "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U (Fun f ss)"
        by (rule Fun.prems(3))
    qed
  next
    case False
    with Fun.prems(1) have nonroot: "(Fun f ss,v) \<in> csnrstep \<mu> R"
      unfolding csstep_root_nonroot by blast
    from csnrstep_FunE[OF nonroot]
    obtain i ts where i: "i < length ss" "i \<in> \<mu> (f,length ss)"
      and v: "v = Fun f ts" and len: "length ts = length ss"
      and child_step: "(ss ! i,ts ! i) \<in> csstep \<mu> R"
      and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
        ts ! j = ss ! j" by blast
    from child_step have child_fun: "is_Fun (ss ! i)"
      by (cases "ss ! i", use csstep_Var_empty_wf[OF wf] in auto)
    have child_SN: "SN_on (csstep \<mu> R) {ss ! i}"
    proof (rule disjE[OF Fun.prems(2)])
      assume T: "Fun f ss \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      have sub: "mu_supt \<mu> (Fun f ss) (ss ! i)"
        unfolding mu_supt_def using i child_fun
        by (intro exI[of _ i] exI[of _ "[]"], cases "ss ! i", auto)
      show ?thesis using T sub unfolding mu_Tinf_def by blast
    next
      assume SN: "SN_on (csstep \<mu> R) {Fun f ss}"
      show ?thesis
      proof (cases "ss ! i")
        case (Var x)
        show ?thesis unfolding Var by (rule SN_on_csstep_Var[OF wf])
      next
        case (Fun g us)
        have pos: "[i] \<in> mu_poss \<mu> (Fun f ss)" using i Fun by simp
        from SN_on_mu_pos[OF wf pos SN]
        show ?thesis using i by simp
      qed
    qed
    have child_unhidable:
        "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U (ss ! i)"
    proof (rule muterm_unhidable_active_subterm[OF Fun.prems(3)])
      show "Fun f ss = ss ! i \<or> mu_supt \<mu> (Fun f ss) (ss ! i)"
        unfolding mu_supt_def using i child_fun
        by (intro disjI2 exI[of _ i] exI[of _ "[]"], cases "ss ! i", auto)
    qed
    have changed_unhidable:
        "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U (ts ! i)"
      by (rule Fun.hyps[OF nth_mem[OF i(1)] child_step disjI2[OF child_SN]
        child_unhidable])
    show ?thesis unfolding v is_muterm_unhidable_def
    proof (intro allI impI)
      fix s t
      assume component: "muterm_frozen_component_on \<mu> (Fun f ts) s"
        and active: "s = t \<or> mu_supt \<mu> s t"
        and tT: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      from component[unfolded muterm_frozen_component_on_Fun]
      show "(s,sharp_term shp t) \<in> rstep U"
      proof
        assume active_comp: "\<exists>j<length ts. j \<in> \<mu> (f,length ts) \<and>
          muterm_frozen_component_on \<mu> (ts ! j) s"
        then obtain j where j: "j < length ts" "j \<in> \<mu> (f,length ts)"
          and comp: "muterm_frozen_component_on \<mu> (ts ! j) s" by blast
        show ?thesis
        proof (cases "j = i")
          case True
          from changed_unhidable comp[unfolded True] active tT
          show ?thesis unfolding is_muterm_unhidable_def by blast
        next
          case False
          have js: "j < length ss" using j len by simp
          have old: "muterm_frozen_component_on \<mu> (Fun f ss) s"
            unfolding muterm_frozen_component_on_Fun
          proof (intro disjI1 exI[of _ j] conjI)
            show "j < length ss" by (rule js)
            show "j \<in> \<mu> (f, length ss)" using j(2) len by simp
            show "muterm_frozen_component_on \<mu> (ss ! j) s"
              using comp same[OF js False] by simp
          qed
          from Fun.prems(3) old active tT show ?thesis
            unfolding is_muterm_unhidable_def by blast
        qed
      next
        assume frozen_comp: "\<exists>j<length ts. j \<notin> \<mu> (f,length ts) \<and>
          (s = ts ! j \<or> muterm_frozen_component_on \<mu> (ts ! j) s)"
        then obtain j where j: "j < length ts" "j \<notin> \<mu> (f,length ts)"
          and comp: "s = ts ! j \<or>
            muterm_frozen_component_on \<mu> (ts ! j) s" by blast
        have ji: "j \<noteq> i" using j i len by auto
        have js: "j < length ss" using j len by simp
        have replace: "ts ! j = ss ! j" by (rule same[OF js ji])
        have frozen_child:
            "muterm_frozen_root_on \<mu> (Fun f ss) (ss ! j)"
          unfolding muterm_frozen_root_on_Fun
        proof (intro disjI1 exI[of _ j] conjI)
          show "j < length ss" by (rule js)
          show "j \<notin> \<mu> (f, length ss)" using j(2) len by simp
          show "ss ! j = ss ! j" by (rule refl)
        qed
        have old: "muterm_frozen_component_on \<mu> (Fun f ss) s"
        proof (rule_tac P = "s = ts ! j" and
            Q = "muterm_frozen_component_on \<mu> (ts ! j) s" in HOL.disjE)
          show "s = ts ! j \<or>
              muterm_frozen_component_on \<mu> (ts ! j) s" by (rule comp)
        next
          assume eq: "s = ts ! j"
          have eq': "s = ss ! j" using eq replace by simp
          have root_s: "muterm_frozen_root_on \<mu> (Fun f ss) s"
            using frozen_child eq' by simp
          show ?thesis
            by (rule muterm_frozen_component_on.direct[OF root_s])
        next
          assume component:
              "muterm_frozen_component_on \<mu> (ts ! j) s"
          have component':
              "muterm_frozen_component_on \<mu> (ss ! j) s"
            using component replace by simp
          show ?thesis
            by (rule muterm_frozen_component_on.nested[
              OF frozen_child component'])
        qed
        from Fun.prems(3) old active tT show ?thesis
          unfolding is_muterm_unhidable_def by blast
      qed
    qed
  qed
qed

lemma csrstep_muterm_unhiding_preserve:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and step: "(u,v) \<in> csrstep \<mu> R"
    and uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and vT: "v \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and unhidable: "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U u"
  shows "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U v"
proof (rule csrstep_muterm_unhiding_preserve_finite[
    OF wf defs cover step _ unhidable])
  fix x q l r \<sigma>
  assume lr: "(l,r) \<in> R" and src: "u = l \<cdot> \<sigma>"
    and x: "x \<in> mu_vars_term \<mu> l"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  from wf lr have lhs: "is_Fun l" unfolding wf_trs_def by (cases l, auto)
  show "SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
    by (rule mu_Tinf_SN_on_active_subst_mu_subterm[
      OF lhs uT[unfolded src] x q])
qed

definition muterm_unhiding_preserving_on ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow>
    ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> bool"
where
  "muterm_unhiding_preserving_on shp \<mu> R U \<longleftrightarrow>
    (\<forall>u v. (u,v) \<in> csstep \<mu> R \<longrightarrow>
      u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<longrightarrow>
      is_muterm_unhidable shp \<mu> (csstep \<mu> R) U u \<longrightarrow>
      is_muterm_unhidable shp \<mu> (csstep \<mu> R) U v)"

lemma muterm_unhiding_preserving_on_from_coverage:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
  shows "muterm_unhiding_preserving_on shp \<mu> R U"
  unfolding muterm_unhiding_preserving_on_def
  by (intro allI impI, rule csstep_muterm_unhiding_preserve_guarded[
      OF wf defs cover _ disjI1], assumption+)

lemma muterm_unhiding_preserving_steps:
  assumes wf: "wf_trs R"
    and preserving: "muterm_unhiding_preserving_on shp \<mu> R U"
    and steps: "(u,v) \<in> (csnrstep \<mu> R)\<^sup>*"
    and hp: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U u"
    and vT: "v \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U v"
  using steps hp vT
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have yz: "(y,z) \<in> csstep \<mu> R"
    using step.hyps(2) unfolding csstep_root_nonroot by auto
  from step.prems(2) have notSN_z: "\<not> SN_on (csstep \<mu> R) {z}"
    unfolding mu_Tinf_def by auto
  have notSN_y: "\<not> SN_on (csstep \<mu> R) {y}"
    by (rule step_notSN_on_source[OF yz notSN_z])
  from step.prems(1) have uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  have yT: "y \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf step.hyps(1) uT notSN_y])
  have hp_y: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U y"
    by (rule step.hyps(3)[OF step.prems(1) yT])
  from hp_y have unhidable_y:
      "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U y"
    unfolding has_muterm_unhiding_property_def by auto
  have unhidable_z: "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U z"
    using preserving yz yT unhidable_y
    unfolding muterm_unhiding_preserving_on_def by blast
  show ?case unfolding has_muterm_unhiding_property_def
    using step.prems(2) unhidable_z by blast
qed

lemma muterm_collapsing_instance:
  assumes cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R" and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l" and lhs: "is_Fun l"
  shows "(sharp_term shp (l \<cdot> \<sigma>), \<sigma> x) \<in> rrstep P"
proof -
  from csr_rta08_collapsing_CSDP_onI[OF lr xr xl]
  have pair: "(sharp_term shp l, Var x) \<in> P"
    using muterm_unhiding_coverage_collapsing[OF cover] by blast
  have sharp: "sharp_term shp (l \<cdot> \<sigma>) = sharp_term shp l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  show ?thesis using pair sharp by auto
qed

lemma csrstep_muterm_unhiding_progress:
  assumes wf: "wf_trs R"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and hp: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U s"
    and notSN: "\<not> SN_on (csstep \<mu> R) {v}"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and preserving: "muterm_unhiding_preserving_on shp \<mu> R U"
  shows "\<exists>u. has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U u \<and>
    (v = u \<or> mu_supt \<mu> v u) \<and>
    (sharp_term shp s,sharp_term shp u) \<in>
      (rstep (R \<union> U))\<^sup>* O rrstep P O (rstep (R \<union> U))\<^sup>*"
proof -
  from root obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and v: "v = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l" and vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by (cases l, auto)
  from hp have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and unhidable_s: "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U s"
    unfolding has_muterm_unhiding_property_def by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have unhidable_v: "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U v"
    using preserving sv sT unhidable_s
    unfolding muterm_unhiding_preserving_on_def by blast
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded v]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f,length us)"
    and uT: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  let ?u = "(r \<cdot> \<sigma>) |_ p"
  have active_u: "v = ?u \<or> mu_supt \<mu> v ?u"
  proof (cases p)
    case Nil
    with v show ?thesis by simp
  next
    case (Cons i q)
    have pos: "i # q \<in> mu_poss \<mu> (r \<cdot> \<sigma>)"
      using p_mu Cons mu_fun_poss_imp_mu_poss by blast
    have sub: "(r \<cdot> \<sigma>) |_ (i # q) = ?u" unfolding Cons by simp
    show ?thesis unfolding v mu_supt_def using pos sub by blast
  qed
  have unhidable_u: "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U ?u"
    by (rule muterm_unhidable_active_subterm[OF unhidable_v active_u])
  have hp_u: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U ?u"
    unfolding has_muterm_unhiding_property_def using uT unhidable_u by blast
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  have connection: "(sharp_term shp s,sharp_term shp ?u) \<in>
      (rstep (R \<union> U))\<^sup>* O rrstep P O (rstep (R \<union> U))\<^sup>*"
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "?u = (r |_ p) \<cdot> \<sigma>" by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where
      rp0: "r |_ p = Fun g ts" using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts"
      and len: "length us = length ts" by auto
    from defs def len have fD: "(f,length ts) \<in> D" by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p"
        unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l" using iq mu_poss_imp_poss by blast
      have sub_eq: "(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>"
        using subt_at_subst[OF iq_poss] sub_l by simp
      have "mu_supt \<mu> (l \<cdot> \<sigma>) ((r |_ p) \<cdot> \<sigma>)"
        unfolding mu_supt_def
        by (intro exI[of _ i] exI[of _ q],
            insert mu_poss_subst_lift[OF iq, of \<sigma>] sub_eq, auto)
      with sT have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        unfolding s mu_Tinf_def by blast
      moreover from uT have "\<not> SN_on (csstep \<mu> R) {?u}"
        unfolding mu_Tinf_def by auto
      ultimately show False unfolding sub_subst by contradiction
    qed
    have dp: "(sharp_term shp (l \<cdot> \<sigma>),
        sharp_term shp ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep P"
    proof -
      have base: "(sharp_term shp (l \<cdot> \<sigma>),
          sharp_term shp ((r |_ p) \<cdot> \<sigma>)) \<in>
          rrstep (mu_CSDP_on shp \<mu> D R)"
        by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
      show ?thesis
        using base rrstep_mono[OF muterm_unhiding_coverage_mu[OF cover]] by blast
    qed
    show ?thesis unfolding s sub_subst using dp by blast
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> ?u = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x" and x_r: "x \<in> vars_term r"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and u: "?u = \<sigma> x |_ q2" by blast
    have xr_mu: "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    show ?thesis
    proof (cases "x \<in> mu_vars_term \<mu> l")
      case True
      have "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
        by (rule mu_Tinf_SN_on_active_subst_mu_subterm[
          OF lhs sT[unfolded s] True q2])
      moreover from uT have "\<not> SN_on (csstep \<mu> R) {?u}"
        unfolding mu_Tinf_def by auto
      ultimately show ?thesis unfolding u by contradiction
    next
      case False
      have frozen_l: "muterm_frozen_root_on \<mu> l (Var x)"
        by (rule muterm_unhiding_safe_migrating[OF cover lr xr_mu False])
      have frozen_inst: "muterm_frozen_root_on \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
        using muterm_frozen_root_subst[OF frozen_l, of \<sigma>] by simp
      have active_xu: "\<sigma> x = ?u \<or> mu_supt \<mu> (\<sigma> x) ?u"
      proof (cases q2)
        case Nil
        with u show ?thesis by simp
      next
        case (Cons i qs)
        have pos: "i # qs \<in> mu_poss \<mu> (\<sigma> x)"
          using q2 Cons mu_fun_poss_imp_mu_poss by blast
        have sub: "\<sigma> x |_ (i # qs) = ?u" using u Cons by simp
        show ?thesis unfolding mu_supt_def using pos sub by blast
      qed
      have frozen_component:
          "muterm_frozen_component_on \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
        by (rule muterm_frozen_component_on.direct[OF frozen_inst])
      have unhide: "(\<sigma> x,sharp_term shp ?u) \<in> rstep U"
        using unhidable_s frozen_component active_xu uT unfolding s
          is_muterm_unhidable_def by blast
      have pair: "(sharp_term shp (l \<cdot> \<sigma>),\<sigma> x) \<in> rrstep P"
        by (rule muterm_collapsing_instance[OF cover lr xr_mu False lhs])
      have Usub: "rstep U \<subseteq> rstep (R \<union> U)"
        by (rule rstep_mono, auto)
      have weak: "(\<sigma> x,sharp_term shp ?u) \<in> (rstep (R \<union> U))\<^sup>*"
        using Usub unhide by auto
      show ?thesis unfolding s using pair weak by blast
    qed
  qed
  show ?thesis using hp_u active_u connection by blast
qed

lemma muterm_unhiding_relstep:
  assumes wf: "wf_trs R"
    and hp: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and preserving: "muterm_unhiding_preserving_on shp \<mu> R U"
  shows "\<exists>u. has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U u \<and>
    (sharp_term shp t,sharp_term shp u) \<in>
      ((rstep (R \<union> U))\<^sup>* O rrstep P O (rstep (R \<union> U))\<^sup>*)\<^sup>+"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and unhidable_t: "is_muterm_unhidable shp \<mu> (csstep \<mu> R) U t"
    unfolding has_muterm_unhiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U s"
    by (rule muterm_unhiding_preserving_steps[OF wf preserving pref hp sT])
  from csrstep_muterm_unhiding_progress[
      OF wf root hp_s notSN_v defs cover preserving]
  obtain u where hp_u: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U u"
    and path: "(sharp_term shp s,sharp_term shp u) \<in>
      (rstep (R \<union> U))\<^sup>* O rrstep P O (rstep (R \<union> U))\<^sup>*"
    by blast
  have prefR: "(sharp_term shp t,sharp_term shp s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have Rsub: "rstep R \<subseteq> rstep (R \<union> U)"
    by (rule rstep_mono, auto)
  have prefRU: "(sharp_term shp t,sharp_term shp s) \<in>
      (rstep (R \<union> U))\<^sup>*"
    using prefR rtrancl_mono[OF Rsub] by blast
  let ?A = "(rstep (R \<union> U))\<^sup>* O rrstep P O (rstep (R \<union> U))\<^sup>*"
  have combined: "(sharp_term shp t,sharp_term shp u) \<in> ?A"
  proof -
    from path obtain a b where sa: "(sharp_term shp s,a) \<in> (rstep (R \<union> U))\<^sup>*"
      and ab: "(a,b) \<in> rrstep P"
      and bu: "(b,sharp_term shp u) \<in> (rstep (R \<union> U))\<^sup>*"
      by auto
    have ta: "(sharp_term shp t,a) \<in> (rstep (R \<union> U))\<^sup>*"
      by (rule rtrancl_trans[OF prefRU sa])
    show ?thesis using ta ab bu by blast
  qed
  have trancl: "(sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule trancl.r_into_trancl[OF combined])
  show ?thesis using hp_u trancl by blast
qed

theorem finite_muterm_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and preserving: "muterm_unhiding_preserving_on shp \<mu> R U"
    and fin: "finite_dpp (False,False,P,{},{},{},R \<union> U)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where t0T: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  have hp0: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  let ?A = "(rstep (R \<union> U))\<^sup>* O rrstep P O (rstep (R \<union> U))\<^sup>*"
  have step_ex: "\<And>t. has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U t \<Longrightarrow>
    \<exists>u. has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U u \<and>
      (sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule muterm_unhiding_relstep[OF wf _ defs cover preserving])
  have all_ex: "\<forall>t. \<exists>u.
    has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U t \<longrightarrow>
    has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U u \<and>
      (sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+" using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
    "\<And>t. has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U t \<Longrightarrow>
      has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U (nxt t) \<and>
      (sharp_term shp t,sharp_term shp (nxt t)) \<in> ?A\<^sup>+" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_hp: "has_muterm_unhiding_property shp \<mu> (csstep \<mu> R) U (ts n)" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] show ?case unfolding ts_def by simp
  qed
  have ts_step: "(sharp_term shp (ts n),sharp_term shp (ts (Suc n))) \<in> ?A\<^sup>+" for n
    using nxt[OF ts_hp[of n]] unfolding ts_def by simp
  define f where "f n = sharp_term shp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?A\<^sup>+"
    unfolding f_def using ts_step by simp
  have "\<not> SN (?A\<^sup>+)" unfolding SN_defs using chain by blast
  moreover from fin have rel: "SN_rel (rrstep P) (rstep (R \<union> U))"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  then have "SN ?A" unfolding SN_rel_on_def .
  then have "SN (?A\<^sup>+)" by (rule SN_imp_SN_trancl)
  ultimately show False by contradiction
qed

corollary finite_muterm_exact_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and fin: "finite_dpp (False,False,P,{},{},{},R \<union> U)"
  shows "SN (csstep \<mu> R)"
  by (rule finite_muterm_CSDP_imp_SN_csstep[
      OF wf defs cover muterm_unhiding_preserving_on_from_coverage[
        OF wf defs cover] fin])

(* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (*

text \<open>
  The four-component CS problems of Guti\<acute>errez and Lucas keep the
  ordinary rules and the unhiding rules separate.  The latter are used only
  after a collapsing pair.  For certification it is sound (and deliberately
  conservative) to forget that restriction after checking the transformation:
  an ordinary DP problem over @{term "R \<union> S"} then over-approximates every
  such CS chain.

  The semantic coverage predicate below permits a finite certificate to use a
  compressed unhiding rules from a hidden context instance to the corresponding
  marked hidden call.
  The executable transformation checker introduced with the proof parser
  establishes this predicate from the finite rules printed in the certificate.
\<close>

definition innermost_unhiding_csdp_coverage ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> 'f sig \<Rightarrow>
    ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> bool"
where
  "innermost_unhiding_csdp_coverage shp \<mu> D R P S \<longleftrightarrow>
    mu_CSDP_on shp \<mu> D R \<subseteq> P \<and>
    csr_rta08_collapsing_CSDP_on shp \<mu> R \<subseteq> P \<and>
    (\<forall>f ts i. hides_position_on \<mu> D R (f,length ts) i \<longrightarrow>
      i < length ts \<longrightarrow> (Fun f ts, ts ! i) \<in> rstep S) \<and>
    (\<forall>h. hidden_term_on \<mu> D R h \<longrightarrow>
      (h, sharp_term shp h) \<in> P)"

lemma innermost_unhiding_csdp_coverage_mu:
  assumes "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
  shows "mu_CSDP_on shp \<mu> D R \<subseteq> P"
  using assms unfolding innermost_unhiding_csdp_coverage_def by auto

lemma innermost_unhiding_csdp_coverage_collapsing:
  assumes "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
  shows "csr_rta08_collapsing_CSDP_on shp \<mu> R \<subseteq> P"
  using assms unfolding innermost_unhiding_csdp_coverage_def by auto

lemma innermost_unhiding_collapsing_instance:
  assumes cover: "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
  shows "(sharp_term shp (l \<cdot> \<sigma>), \<sigma> x) \<in> rrstep P"
proof -
  from csr_rta08_collapsing_CSDP_onI[OF lr xr xl]
  have pair: "(sharp_term shp l, Var x) \<in> P"
    using innermost_unhiding_csdp_coverage_collapsing[OF cover] by blast
  have sharp: "sharp_term shp (l \<cdot> \<sigma>) = sharp_term shp l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  show ?thesis using pair sharp by auto
qed

lemma innermost_unhiding_collapsing_path:
  assumes cover: "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
    and C: "hiding_context_on \<mu> D R C"
    and hidden: "hidden_term_on \<mu> D R h"
    and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
  shows "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp (h \<cdot> \<tau>)) \<in>
    ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  have pair: "(sharp_term shp (l \<cdot> \<sigma>), \<sigma> x) \<in> rrstep P"
    by (rule innermost_unhiding_collapsing_instance[OF cover lr xr xl lhs])
  have peel: "(C\<langle>h \<cdot> \<tau>\<rangle>,h \<cdot> \<tau>) \<in> (rstep S)\<^sup>*"
    using C
  proof (induct rule: hiding_context_on.induct)
    case hole
    then show ?case by simp
  next
    case (more f bef aft C)
    let ?ts = "bef @ C\<langle>h \<cdot> \<tau>\<rangle> # aft"
    have hide: "hides_position_on \<mu> D R (f,length ?ts) (length bef)"
      using more.hyps(1) by simp
    have pos: "length bef < length ?ts" by simp
    from cover hide pos have raw:
      "(Fun f ?ts, ?ts ! length bef) \<in> rstep S"
      unfolding innermost_unhiding_csdp_coverage_def by blast
    have nth: "?ts ! length bef = C\<langle>h \<cdot> \<tau>\<rangle>" by simp
    from raw have step:
      "(Fun f ?ts, C\<langle>h \<cdot> \<tau>\<rangle>) \<in> rstep S"
      unfolding nth .
    from step more.hyps(3) show ?case by auto
  qed
  from cover hidden have mark0: "(h,sharp_term shp h) \<in> P"
    unfolding innermost_unhiding_csdp_coverage_def by blast
  have mark: "(h \<cdot> \<tau>,sharp_term shp (h \<cdot> \<tau>)) \<in> rrstep P"
    using mark0 hidden_term_on_is_Fun[OF hidden] by (cases h, auto)
  let ?A = "(rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
  have first: "(sharp_term shp (l \<cdot> \<sigma>),h \<cdot> \<tau>) \<in> ?A"
    using pair peel unfolding sx by blast
  have last: "(h \<cdot> \<tau>,sharp_term shp (h \<cdot> \<tau>)) \<in> ?A"
    using mark by blast
  from first last show ?thesis by auto
qed

lemma innermost_unhiding_hidden_substitution_path:
  assumes hp: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    and proper: "s \<rhd> \<sigma> x"
    and inactive: "\<not> mu_supt \<mu> s (\<sigma> x)"
    and active: "\<sigma> x = u \<or> mu_supt \<mu> (\<sigma> x) u"
    and T: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and cover: "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
  shows "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp u) \<in>
    ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  from hp have hidden_instance:
    "\<And>s' t'. s \<rhd> s' \<Longrightarrow> \<not> mu_supt \<mu> s s' \<Longrightarrow>
      (s' = t' \<or> mu_supt \<mu> s' t') \<Longrightarrow>
      t' \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
      \<exists>C h \<tau>. hiding_context_on \<mu> D R C \<and>
        hidden_term_on \<mu> D R h \<and>
        s' = C\<langle>h \<cdot> \<tau>\<rangle> \<and> t' = h \<cdot> \<tau>"
    unfolding has_hiding_property_def by auto
  from hidden_instance[OF proper inactive active T]
  obtain C h \<tau> where C: "hiding_context_on \<mu> D R C"
    and hidden: "hidden_term_on \<mu> D R h"
    and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
    and uh: "u = h \<cdot> \<tau>" by blast
  from innermost_unhiding_collapsing_path[
      where C=C and h=h and \<sigma>=\<sigma> and \<tau>=\<tau> and x=x and l=l and r=r,
      OF cover lr xr xl lhs C hidden sx]
  show ?thesis unfolding uh .
qed

lemma innermost_unhiding_original_rhs_case:
  assumes lr: "(l,r) \<in> R" and lhs: "is_Fun l"
    and p_r: "p \<in> mu_fun_poss \<mu> r"
    and rp: "r |_ p = Fun f ts" and fD: "(f,length ts) \<in> D"
    and ns: "\<not> mu_supt \<mu> l (r |_ p)"
    and cover: "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and s: "s = l \<cdot> \<sigma>" and u: "u = (r |_ p) \<cdot> \<sigma>"
    and T: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "t = u \<or> mu_supt \<mu> t u"
  shows "\<exists>v. v \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (t = v \<or> mu_supt \<mu> t v) \<and>
    (sharp_term shp s,sharp_term shp v) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  have dp0:
    "(sharp_term shp (l \<cdot> \<sigma>), sharp_term shp ((r |_ p) \<cdot> \<sigma>))
      \<in> rrstep (mu_CSDP_on shp \<mu> D R)"
    by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
  have mono: "rrstep (mu_CSDP_on shp \<mu> D R) \<subseteq> rrstep P"
    by (rule rrstep_mono[OF innermost_unhiding_csdp_coverage_mu[OF cover]])
  from dp0 mono have dp: "(sharp_term shp s,sharp_term shp u) \<in> rrstep P"
    unfolding s u by auto
  have one: "(sharp_term shp s,sharp_term shp u) \<in>
      (rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
    using dp by blast
  show ?thesis
    using T active one by blast
qed

lemma innermost_unhiding_active_substitution_finite:
  assumes lhs: "is_Fun l"
    and source: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "x \<in> mu_vars_term \<mu> l"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
  by (rule mu_Tinf_SN_on_active_subst_mu_subterm[OF lhs source active q])

lemma rtrancl_prefix_relcomp_trancl:
  assumes prefix: "(x,y) \<in> A\<^sup>*"
    and chain: "(y,z) \<in> (A\<^sup>* O B O A\<^sup>*)\<^sup>+"
  shows "(x,z) \<in> (A\<^sup>* O B O A\<^sup>*)\<^sup>+"
proof -
  let ?C = "A\<^sup>* O B O A\<^sup>*"
  from chain show ?thesis
  proof (induct rule: trancl_induct)
    case (base z)
    then obtain a b where ya: "(y,a) \<in> A\<^sup>*"
      and ab: "(a,b) \<in> B" and bz: "(b,z) \<in> A\<^sup>*"
      by auto
    have xa: "(x,a) \<in> A\<^sup>*" by (rule rtrancl_trans[OF prefix ya])
    have "(x,z) \<in> ?C" using xa ab bz by auto
    then show ?case by (rule trancl.r_into_trancl)
  next
    case (step y z)
    show ?case by (rule trancl_into_trancl[OF step.hyps(3) step.hyps(2)])
  qed
qed

lemma csrstep_hiding_rhs_imp_innermost_unhiding_relstep:
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> csrstep \<mu> R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (t = u \<or> mu_supt \<mu> t u) \<and>
    (sharp_term shp s,sharp_term shp u) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    and vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by (cases l, auto)
  from hp have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  let ?u = "(r \<cdot> \<sigma>) |_ p"
  have active_rhs: "t = ?u \<or> mu_supt \<mu> t ?u"
  proof (cases p)
    case Nil
    with t show ?thesis by simp
  next
    case (Cons i q)
    have pos: "i # q \<in> mu_poss \<mu> (r \<cdot> \<sigma>)"
      using p_mu Cons mu_fun_poss_imp_mu_poss by blast
    have "(r \<cdot> \<sigma>) |_ (i # q) = ?u" unfolding Cons by simp
    then have "mu_supt \<mu> (r \<cdot> \<sigma>) ?u"
      unfolding mu_supt_def using pos by blast
    with t show ?thesis by simp
  qed
  from T_p have notSN_p: "\<not> SN_on (csstep \<mu> R) {?u}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "?u = (r |_ p) \<cdot> \<sigma>" by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where
      rp0: "r |_ p = Fun g ts" using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts"
      and len: "length us = length ts" by auto
    from defs def len have fD: "(f, length ts) \<in> D" by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p"
        unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l" using iq mu_poss_imp_poss by blast
      have sub_eq: "(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>"
        using subt_at_subst[OF iq_poss] sub_l by simp
      have "mu_supt \<mu> (l \<cdot> \<sigma>) ((r |_ p) \<cdot> \<sigma>)"
        unfolding mu_supt_def
        by (intro exI[of _ i] exI[of _ q],
            insert mu_poss_subst_lift[OF iq, of \<sigma>] sub_eq, auto)
      with sT have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False by simp
    qed
    show ?thesis
      by (rule innermost_unhiding_original_rhs_case[
        OF lr lhs p_r rp fD ns cover s sub_subst T_p active_rhs])
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> ?u = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and x_r: "x \<in> vars_term r"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and u: "?u = \<sigma> x |_ q2" by blast
    have xr_mu: "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    show ?thesis
    proof (cases "x \<in> mu_vars_term \<mu> l")
      case True
      have "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
        by (rule innermost_unhiding_active_substitution_finite[
          OF lhs sT[unfolded s] True q2])
      with notSN_p u show ?thesis by simp
    next
      case False
      note inactive_l = False
      from vars x_r have x_l: "x \<in> vars_term l" by auto
      from lhs x_l have l_supt_x: "l \<rhd> Var x"
        using supteq_Var[of x l] unfolding supt_supteq_conv by (cases l, auto)
      have s_supt_x: "s \<rhd> \<sigma> x"
        using supt_subst[OF l_supt_x, of \<sigma>] unfolding s by simp
      have not_mu_supt_x: "\<not> mu_supt \<mu> s (\<sigma> x)"
      proof
        assume active: "mu_supt \<mu> s (\<sigma> x)"
        from sT active have snx: "SN_on (csstep \<mu> R) {\<sigma> x}"
          unfolding mu_Tinf_def by auto
        have snu: "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
          by (rule SN_on_mu_subterm[OF wf q2 snx])
        with notSN_p u show False by simp
      qed
      have active_u: "\<sigma> x = ?u \<or> mu_supt \<mu> (\<sigma> x) ?u"
      proof (cases q2)
        case Nil
        with u show ?thesis by simp
      next
        case (Cons i q)
        from q2 have ip: "i # q \<in> mu_poss \<mu> (\<sigma> x)"
          using mu_fun_poss_imp_mu_poss Cons by blast
        have sub: "\<sigma> x |_ (i # q) = ?u" using u Cons by simp
        show ?thesis unfolding mu_supt_def using ip sub by blast
      qed
      have path: "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp ?u) \<in>
        ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
        by (rule innermost_unhiding_hidden_substitution_path[
          where \<sigma>=\<sigma> and x=x and u="?u" and s=s and l=l and r=r,
          OF hp s_supt_x not_mu_supt_x active_u T_p cover lr xr_mu
            inactive_l lhs])
      show ?thesis
      proof (intro exI[of _ ?u] conjI)
        show "?u \<in> mu_Tinf \<mu> (csstep \<mu> R)" by (rule T_p)
        show "t = ?u \<or> mu_supt \<mu> t ?u" by (rule active_rhs)
        show "(sharp_term shp s,sharp_term shp ?u) \<in>
          ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
          unfolding s by (rule path)
      qed
    qed
  qed
qed

lemma hiding_imp_innermost_unhiding_relstep:
  assumes wf: "wf_trs R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
  shows "\<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
    (sharp_term shp t,sharp_term shp u) \<in>
      ((rstep (R \<union> S))\<^sup>* O rrstep P O (rstep (R \<union> S))\<^sup>*)\<^sup>+"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    by (rule csnrsteps_hiding_property_preserve[OF wf defs pref hp sT])
  from csrstep_hiding_rhs_imp_innermost_unhiding_relstep[
      OF wf root hp_s notSN_v defs cover]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "v = u \<or> mu_supt \<mu> v u"
    and path: "(sharp_term shp s,sharp_term shp u) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+" by blast
  have hp_u: "has_hiding_property \<mu> D R (csstep \<mu> R) u"
    by (rule csrstep_hiding_property_active_target[OF wf defs root hp_s active uT])
  have prefR: "(sharp_term shp t,sharp_term shp s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have Rsub: "rstep R \<subseteq> rstep (R \<union> S)"
    by (rule rstep_mono, auto)
  have Ssub: "rstep S \<subseteq> rstep (R \<union> S)"
    by (rule rstep_mono, auto)
  have pref': "(sharp_term shp t,sharp_term shp s) \<in> (rstep (R \<union> S))\<^sup>*"
    using prefR rtrancl_mono[OF Rsub] by blast
  let ?AS = "(rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
  let ?A = "(rstep (R \<union> S))\<^sup>* O rrstep P O (rstep (R \<union> S))\<^sup>*"
  have mono: "?AS \<subseteq> ?A"
    using rtrancl_mono[OF Ssub] by blast
  have path': "(sharp_term shp s,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule trancl_mono[OF path mono])
  have result: "(sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule rtrancl_prefix_relcomp_trancl[OF pref' path'])
  show ?thesis by (intro exI[of _ u] conjI, rule hp_u, rule result)
qed

theorem finite_innermost_unhiding_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and fin: "finite_dpp (False,False,P,{},{},{},R \<union> S)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where t0T: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  have hp0: "has_hiding_property \<mu> D R (csstep \<mu> R) t0"
    by (rule Tinf_has_hiding_property[OF t0T])
  let ?A = "(rstep (R \<union> S))\<^sup>* O rrstep P O (rstep (R \<union> S))\<^sup>*"
  have step_ex: "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
    \<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
      (sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule hiding_imp_innermost_unhiding_relstep[OF wf _ defs cover])
  have all_ex: "\<forall>t. \<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) t \<longrightarrow>
    has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
      (sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+" using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
    "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
      has_hiding_property \<mu> D R (csstep \<mu> R) (nxt t) \<and>
      (sharp_term shp t,sharp_term shp (nxt t)) \<in> ?A\<^sup>+" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_hp: "has_hiding_property \<mu> D R (csstep \<mu> R) (ts n)" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] show ?case unfolding ts_def by simp
  qed
  have ts_step: "(sharp_term shp (ts n),sharp_term shp (ts (Suc n))) \<in> ?A\<^sup>+" for n
    using nxt[OF ts_hp[of n]] unfolding ts_def by simp
  define f where "f n = sharp_term shp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?A\<^sup>+" unfolding f_def using ts_step by simp
  have "\<not> SN (?A\<^sup>+)" unfolding SN_defs using chain by blast
  moreover from fin have rel: "SN_rel (rrstep P) (rstep (R \<union> S))"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  then have "SN ?A" unfolding SN_rel_on_def .
  then have "SN (?A\<^sup>+)" by (rule SN_imp_SN_trancl)
  ultimately show False by contradiction
qed


text \<open>
  MU-TERM compresses a hiding-context projection followed by marking the
  exposed defined call into one weak unhiding step.  This coverage predicate
  records precisely that semantic obligation; the executable checker below
  derives it from the finite rules in the certificate.
\<close>

definition muterm_innermost_unhiding_csdp_coverage ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> 'f sig \<Rightarrow>
    ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> bool"
where
  "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S \<longleftrightarrow>
    mu_CSDP_on shp \<mu> D R \<subseteq> P \<and>
    csr_rta08_collapsing_CSDP_on shp \<mu> R \<subseteq> P \<and>
    (\<forall>C h \<sigma>. hiding_context_on \<mu> D R C \<longrightarrow>
      hidden_term_on \<mu> D R h \<longrightarrow>
      (C\<langle>h \<cdot> \<sigma>\<rangle>, sharp_term shp (h \<cdot> \<sigma>)) \<in> (rstep S)\<^sup>*)"

lemma muterm_innermost_unhiding_csdp_coverage_mu:
  assumes "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
  shows "mu_CSDP_on shp \<mu> D R \<subseteq> P"
  using assms unfolding muterm_innermost_unhiding_csdp_coverage_def by auto

lemma muterm_innermost_unhiding_csdp_coverage_collapsing:
  assumes "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
  shows "csr_rta08_collapsing_CSDP_on shp \<mu> R \<subseteq> P"
  using assms unfolding muterm_innermost_unhiding_csdp_coverage_def by auto

lemma muterm_innermost_unhiding_collapsing_instance:
  assumes cover: "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and lr: "(l,r) \<in> R" and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l" and lhs: "is_Fun l"
  shows "(sharp_term shp (l \<cdot> \<sigma>), \<sigma> x) \<in> rrstep P"
proof -
  from csr_rta08_collapsing_CSDP_onI[OF lr xr xl]
  have pair: "(sharp_term shp l, Var x) \<in> P"
    using muterm_innermost_unhiding_csdp_coverage_collapsing[OF cover] by blast
  have sharp: "sharp_term shp (l \<cdot> \<sigma>) = sharp_term shp l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  show ?thesis using pair sharp by auto
qed

lemma muterm_innermost_unhiding_collapsing_path:
  assumes cover: "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and lr: "(l,r) \<in> R" and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l" and lhs: "is_Fun l"
    and C: "hiding_context_on \<mu> D R C"
    and hidden: "hidden_term_on \<mu> D R h"
    and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
  shows "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp (h \<cdot> \<tau>)) \<in>
    ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  have pair: "(sharp_term shp (l \<cdot> \<sigma>), \<sigma> x) \<in> rrstep P"
    by (rule muterm_innermost_unhiding_collapsing_instance[OF cover lr xr xl lhs])
  have compressed: "(C\<langle>h \<cdot> \<tau>\<rangle>, sharp_term shp (h \<cdot> \<tau>))
      \<in> (rstep S)\<^sup>*"
    using cover C hidden
    unfolding muterm_innermost_unhiding_csdp_coverage_def by blast
  have one: "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp (h \<cdot> \<tau>)) \<in>
      (rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
    using pair compressed unfolding sx by blast
  show ?thesis by (rule trancl.r_into_trancl[OF one])
qed

lemma muterm_innermost_unhiding_hidden_substitution_path:
  assumes hp: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    and proper: "s \<rhd> \<sigma> x"
    and inactive: "\<not> mu_supt \<mu> s (\<sigma> x)"
    and active: "\<sigma> x = u \<or> mu_supt \<mu> (\<sigma> x) u"
    and T: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and cover: "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
  shows "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp u) \<in>
    ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  from hp have hidden_instance:
    "\<And>s' t'. s \<rhd> s' \<Longrightarrow> \<not> mu_supt \<mu> s s' \<Longrightarrow>
      (s' = t' \<or> mu_supt \<mu> s' t') \<Longrightarrow>
      t' \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
      \<exists>C h \<tau>. hiding_context_on \<mu> D R C \<and>
        hidden_term_on \<mu> D R h \<and>
        s' = C\<langle>h \<cdot> \<tau>\<rangle> \<and> t' = h \<cdot> \<tau>"
    unfolding has_hiding_property_def by auto
  from hidden_instance[OF proper inactive active T]
  obtain C h \<tau> where C: "hiding_context_on \<mu> D R C"
    and hidden: "hidden_term_on \<mu> D R h"
    and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
    and uh: "u = h \<cdot> \<tau>" by blast
  from muterm_innermost_unhiding_collapsing_path[
      where C=C and h=h and \<sigma>=\<sigma> and \<tau>=\<tau> and x=x and l=l and r=r,
      OF cover lr xr xl lhs C hidden sx]
  show ?thesis unfolding uh .
qed

lemma muterm_innermost_unhiding_original_rhs_case:
  assumes lr: "(l,r) \<in> R" and lhs: "is_Fun l"
    and p_r: "p \<in> mu_fun_poss \<mu> r"
    and rp: "r |_ p = Fun f ts" and fD: "(f,length ts) \<in> D"
    and ns: "\<not> mu_supt \<mu> l (r |_ p)"
    and cover: "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and s: "s = l \<cdot> \<sigma>" and u: "u = (r |_ p) \<cdot> \<sigma>"
    and T: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "t = u \<or> mu_supt \<mu> t u"
  shows "\<exists>v. v \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (t = v \<or> mu_supt \<mu> t v) \<and>
    (sharp_term shp s,sharp_term shp v) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  have dp0:
    "(sharp_term shp (l \<cdot> \<sigma>), sharp_term shp ((r |_ p) \<cdot> \<sigma>))
      \<in> rrstep (mu_CSDP_on shp \<mu> D R)"
    by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
  have mono: "rrstep (mu_CSDP_on shp \<mu> D R) \<subseteq> rrstep P"
    by (rule rrstep_mono[OF muterm_innermost_unhiding_csdp_coverage_mu[OF cover]])
  from dp0 mono have dp: "(sharp_term shp s,sharp_term shp u) \<in> rrstep P"
    unfolding s u by auto
  have one: "(sharp_term shp s,sharp_term shp u) \<in>
      (rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
    using dp by blast
  show ?thesis
    using T active one by blast
qed

lemma muterm_innermost_unhiding_active_substitution_finite:
  assumes lhs: "is_Fun l"
    and source: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "x \<in> mu_vars_term \<mu> l"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
  by (rule mu_Tinf_SN_on_active_subst_mu_subterm[OF lhs source active q])

lemma muterm_rtrancl_prefix_relcomp_trancl:
  assumes prefix: "(x,y) \<in> A\<^sup>*"
    and chain: "(y,z) \<in> (A\<^sup>* O B O A\<^sup>*)\<^sup>+"
  shows "(x,z) \<in> (A\<^sup>* O B O A\<^sup>*)\<^sup>+"
proof -
  let ?C = "A\<^sup>* O B O A\<^sup>*"
  from chain show ?thesis
  proof (induct rule: trancl_induct)
    case (base z)
    then obtain a b where ya: "(y,a) \<in> A\<^sup>*"
      and ab: "(a,b) \<in> B" and bz: "(b,z) \<in> A\<^sup>*"
      by auto
    have xa: "(x,a) \<in> A\<^sup>*" by (rule rtrancl_trans[OF prefix ya])
    have "(x,z) \<in> ?C" using xa ab bz by auto
    then show ?case by (rule trancl.r_into_trancl)
  next
    case (step y z)
    show ?case by (rule trancl_into_trancl[OF step.hyps(3) step.hyps(2)])
  qed
qed

lemma csrstep_hiding_rhs_imp_muterm_innermost_unhiding_relstep:
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> csrstep \<mu> R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (t = u \<or> mu_supt \<mu> t u) \<and>
    (sharp_term shp s,sharp_term shp u) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    and vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by (cases l, auto)
  from hp have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  let ?u = "(r \<cdot> \<sigma>) |_ p"
  have active_rhs: "t = ?u \<or> mu_supt \<mu> t ?u"
  proof (cases p)
    case Nil
    with t show ?thesis by simp
  next
    case (Cons i q)
    have pos: "i # q \<in> mu_poss \<mu> (r \<cdot> \<sigma>)"
      using p_mu Cons mu_fun_poss_imp_mu_poss by blast
    have "(r \<cdot> \<sigma>) |_ (i # q) = ?u" unfolding Cons by simp
    then have "mu_supt \<mu> (r \<cdot> \<sigma>) ?u"
      unfolding mu_supt_def using pos by blast
    with t show ?thesis by simp
  qed
  from T_p have notSN_p: "\<not> SN_on (csstep \<mu> R) {?u}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "?u = (r |_ p) \<cdot> \<sigma>" by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where
      rp0: "r |_ p = Fun g ts" using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts"
      and len: "length us = length ts" by auto
    from defs def len have fD: "(f, length ts) \<in> D" by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p"
        unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l" using iq mu_poss_imp_poss by blast
      have sub_eq: "(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>"
        using subt_at_subst[OF iq_poss] sub_l by simp
      have "mu_supt \<mu> (l \<cdot> \<sigma>) ((r |_ p) \<cdot> \<sigma>)"
        unfolding mu_supt_def
        by (intro exI[of _ i] exI[of _ q],
            insert mu_poss_subst_lift[OF iq, of \<sigma>] sub_eq, auto)
      with sT have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False by simp
    qed
    show ?thesis
      by (rule muterm_innermost_unhiding_original_rhs_case[
        OF lr lhs p_r rp fD ns cover s sub_subst T_p active_rhs])
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> ?u = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and x_r: "x \<in> vars_term r"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and u: "?u = \<sigma> x |_ q2" by blast
    have xr_mu: "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    show ?thesis
    proof (cases "x \<in> mu_vars_term \<mu> l")
      case True
      have "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
        by (rule muterm_innermost_unhiding_active_substitution_finite[
          OF lhs sT[unfolded s] True q2])
      with notSN_p u show ?thesis by simp
    next
      case False
      note inactive_l = False
      from vars x_r have x_l: "x \<in> vars_term l" by auto
      from lhs x_l have l_supt_x: "l \<rhd> Var x"
        using supteq_Var[of x l] unfolding supt_supteq_conv by (cases l, auto)
      have s_supt_x: "s \<rhd> \<sigma> x"
        using supt_subst[OF l_supt_x, of \<sigma>] unfolding s by simp
      have not_mu_supt_x: "\<not> mu_supt \<mu> s (\<sigma> x)"
      proof
        assume active: "mu_supt \<mu> s (\<sigma> x)"
        from sT active have snx: "SN_on (csstep \<mu> R) {\<sigma> x}"
          unfolding mu_Tinf_def by auto
        have snu: "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
          by (rule SN_on_mu_subterm[OF wf q2 snx])
        with notSN_p u show False by simp
      qed
      have active_u: "\<sigma> x = ?u \<or> mu_supt \<mu> (\<sigma> x) ?u"
      proof (cases q2)
        case Nil
        with u show ?thesis by simp
      next
        case (Cons i q)
        from q2 have ip: "i # q \<in> mu_poss \<mu> (\<sigma> x)"
          using mu_fun_poss_imp_mu_poss Cons by blast
        have sub: "\<sigma> x |_ (i # q) = ?u" using u Cons by simp
        show ?thesis unfolding mu_supt_def using ip sub by blast
      qed
      have path: "(sharp_term shp (l \<cdot> \<sigma>),sharp_term shp ?u) \<in>
        ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
        by (rule muterm_innermost_unhiding_hidden_substitution_path[
          where \<sigma>=\<sigma> and x=x and u="?u" and s=s and l=l and r=r,
          OF hp s_supt_x not_mu_supt_x active_u T_p cover lr xr_mu
            inactive_l lhs])
      show ?thesis
      proof (intro exI[of _ ?u] conjI)
        show "?u \<in> mu_Tinf \<mu> (csstep \<mu> R)" by (rule T_p)
        show "t = ?u \<or> mu_supt \<mu> t ?u" by (rule active_rhs)
        show "(sharp_term shp s,sharp_term shp ?u) \<in>
          ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+"
          unfolding s by (rule path)
      qed
    qed
  qed
qed

lemma hiding_imp_muterm_innermost_unhiding_relstep:
  assumes wf: "wf_trs R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
  shows "\<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
    (sharp_term shp t,sharp_term shp u) \<in>
      ((rstep (R \<union> S))\<^sup>* O rrstep P O (rstep (R \<union> S))\<^sup>*)\<^sup>+"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    by (rule csnrsteps_hiding_property_preserve[OF wf defs pref hp sT])
  from csrstep_hiding_rhs_imp_muterm_innermost_unhiding_relstep[
      OF wf root hp_s notSN_v defs cover]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "v = u \<or> mu_supt \<mu> v u"
    and path: "(sharp_term shp s,sharp_term shp u) \<in>
      ((rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*)\<^sup>+" by blast
  have hp_u: "has_hiding_property \<mu> D R (csstep \<mu> R) u"
    by (rule csrstep_hiding_property_active_target[OF wf defs root hp_s active uT])
  have prefR: "(sharp_term shp t,sharp_term shp s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have Rsub: "rstep R \<subseteq> rstep (R \<union> S)"
    by (rule rstep_mono, auto)
  have Ssub: "rstep S \<subseteq> rstep (R \<union> S)"
    by (rule rstep_mono, auto)
  have pref': "(sharp_term shp t,sharp_term shp s) \<in> (rstep (R \<union> S))\<^sup>*"
    using prefR rtrancl_mono[OF Rsub] by blast
  let ?AS = "(rstep S)\<^sup>* O rrstep P O (rstep S)\<^sup>*"
  let ?A = "(rstep (R \<union> S))\<^sup>* O rrstep P O (rstep (R \<union> S))\<^sup>*"
  have mono: "?AS \<subseteq> ?A"
    using rtrancl_mono[OF Ssub] by blast
  have path': "(sharp_term shp s,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule trancl_mono[OF path mono])
  have result: "(sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule muterm_rtrancl_prefix_relcomp_trancl[OF pref' path'])
  show ?thesis by (intro exI[of _ u] conjI, rule hp_u, rule result)
qed

theorem finite_muterm_innermost_unhiding_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_innermost_unhiding_csdp_coverage shp \<mu> D R P S"
    and fin: "finite_dpp (False,False,P,{},{},{},R \<union> S)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where t0T: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  have hp0: "has_hiding_property \<mu> D R (csstep \<mu> R) t0"
    by (rule Tinf_has_hiding_property[OF t0T])
  let ?A = "(rstep (R \<union> S))\<^sup>* O rrstep P O (rstep (R \<union> S))\<^sup>*"
  have step_ex: "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
    \<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
      (sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+"
    by (rule hiding_imp_muterm_innermost_unhiding_relstep[OF wf _ defs cover])
  have all_ex: "\<forall>t. \<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) t \<longrightarrow>
    has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
      (sharp_term shp t,sharp_term shp u) \<in> ?A\<^sup>+" using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
    "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
      has_hiding_property \<mu> D R (csstep \<mu> R) (nxt t) \<and>
      (sharp_term shp t,sharp_term shp (nxt t)) \<in> ?A\<^sup>+" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_hp: "has_hiding_property \<mu> D R (csstep \<mu> R) (ts n)" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] show ?case unfolding ts_def by simp
  qed
  have ts_step: "(sharp_term shp (ts n),sharp_term shp (ts (Suc n))) \<in> ?A\<^sup>+" for n
    using nxt[OF ts_hp[of n]] unfolding ts_def by simp
  define f where "f n = sharp_term shp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?A\<^sup>+" unfolding f_def using ts_step by simp
  have "\<not> SN (?A\<^sup>+)" unfolding SN_defs using chain by blast
  moreover from fin have rel: "SN_rel (rrstep P) (rstep (R \<union> S))"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  then have "SN ?A" unfolding SN_rel_on_def .
  then have "SN (?A\<^sup>+)" by (rule SN_imp_SN_trancl)
  ultimately show False by contradiction
qed
*)

fun muterm_frozen_roots_list ::
  "'f muL \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term list"
where
  "muterm_frozen_roots_list \<mu> (Var x) = []"
| "muterm_frozen_roots_list \<mu> (Fun f ts) =
    concat (map (\<lambda>i. if i \<in> mu_of \<mu> (f,length ts)
      then muterm_frozen_roots_list \<mu> (ts ! i)
      else [ts ! i]) [0..<length ts])"

fun muterm_active_defined_calls_list ::
  "'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f,'v) term \<Rightarrow>
    ('f,'v) term list"
where
  "muterm_active_defined_calls_list \<mu> D (Var x) = []"
| "muterm_active_defined_calls_list \<mu> D (Fun f ts) =
    (if (f,length ts) \<in> set D then [Fun f ts] else []) @
    concat (map (\<lambda>i. muterm_active_defined_calls_list \<mu> D (ts ! i))
      [i \<leftarrow> [0..<length ts]. i \<in> mu_of \<mu> (f,length ts)])"

definition muterm_exact_unhiding_rules_list ::
  "('f::{showl,compare_order} \<Rightarrow> 'f) \<Rightarrow> 'f muL \<Rightarrow>
    ('f \<times> nat) list \<Rightarrow> ('f,'v) rules \<Rightarrow> ('f,'v) rules"
where
  "muterm_exact_unhiding_rules_list shp \<mu> D R = remdups
    (concat (map (\<lambda>(l,r). concat (map (\<lambda>h.
      map (\<lambda>t. (h, sharp_term shp t))
        (muterm_active_defined_calls_list \<mu> D h))
      (muterm_frozen_roots_list \<mu> r))) R))"

lemma muterm_frozen_roots_list_set:
  "set (muterm_frozen_roots_list \<mu> r) =
    {h. muterm_frozen_root_on (mu_of \<mu>) r h}"
proof (induct r)
  case (Var x)
  show ?case unfolding muterm_frozen_root_on_def by auto
next
  case (Fun f ts)
  show ?case unfolding muterm_frozen_root_on_Fun
    using Fun by (auto simp: set_concat split: if_splits)
qed

lemma muterm_active_defined_call_on_Fun:
  "muterm_active_defined_call_on \<mu> D (Fun f ts) t \<longleftrightarrow>
    (t = Fun f ts \<and> (f,length ts) \<in> D) \<or>
    (\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_active_defined_call_on \<mu> D (ts ! i) t)"
proof
  assume call: "muterm_active_defined_call_on \<mu> D (Fun f ts) t"
  then obtain p where p: "p \<in> mu_fun_poss \<mu> (Fun f ts)"
    and at: "Fun f ts |_ p = t" and root: "root t \<in> Some ` D"
    unfolding muterm_active_defined_call_on_def by blast
  show "(t = Fun f ts \<and> (f,length ts) \<in> D) \<or>
    (\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_active_defined_call_on \<mu> D (ts ! i) t)"
  proof (cases p)
    case Nil
    from root obtain d where d: "d \<in> D" and rt: "root t = Some d" by blast
    with at Nil have "t = Fun f ts" "d = (f,length ts)" by auto
    with d show ?thesis by blast
  next
    case (Cons i q)
    from p Cons have i: "i < length ts" "i \<in> \<mu> (f,length ts)"
      and q: "q \<in> mu_fun_poss \<mu> (ts ! i)" by auto
    have qat: "ts ! i |_ q = t" using at Cons i by simp
    have "muterm_active_defined_call_on \<mu> D (ts ! i) t"
      unfolding muterm_active_defined_call_on_def using q qat root by blast
    with i show ?thesis by blast
  qed
next
  assume split: "(t = Fun f ts \<and> (f,length ts) \<in> D) \<or>
    (\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_active_defined_call_on \<mu> D (ts ! i) t)"
  show "muterm_active_defined_call_on \<mu> D (Fun f ts) t"
  proof (rule disjE[OF split])
    assume "t = Fun f ts \<and> (f,length ts) \<in> D"
    then show ?thesis unfolding muterm_active_defined_call_on_def by auto
  next
    assume "\<exists>i<length ts. i \<in> \<mu> (f,length ts) \<and>
      muterm_active_defined_call_on \<mu> D (ts ! i) t"
    then obtain i p where i: "i < length ts" "i \<in> \<mu> (f,length ts)"
      and p: "p \<in> mu_fun_poss \<mu> (ts ! i)" and at: "ts ! i |_ p = t"
      and root: "root t \<in> Some ` D"
      unfolding muterm_active_defined_call_on_def by blast
    show ?thesis unfolding muterm_active_defined_call_on_def
      by (intro exI[of _ "i # p"], use i p at root in auto)
  qed
qed

lemma muterm_active_defined_calls_list_set:
  "set (muterm_active_defined_calls_list \<mu> D h) =
    {t. muterm_active_defined_call_on (mu_of \<mu>) (set D) h t}"
proof (induct h)
  case (Var x)
  show ?case unfolding muterm_active_defined_call_on_def by auto
next
  case (Fun f ts)
  show ?case unfolding muterm_active_defined_call_on_Fun
    using Fun by (auto simp: set_concat split: if_splits)
qed

lemma muterm_exact_unhiding_rules_list_set:
  "set (muterm_exact_unhiding_rules_list shp \<mu> D R) =
    {(h,sharp_term shp t) |h t. (\<exists>l r. (l,r) \<in> set R \<and>
      muterm_frozen_root_on (mu_of \<mu>) r h) \<and>
      muterm_active_defined_call_on (mu_of \<mu>) (set D) h t}"
  unfolding muterm_exact_unhiding_rules_list_def
  by (auto simp: set_concat muterm_frozen_roots_list_set
      muterm_active_defined_calls_list_set split: prod.splits)

definition muterm_safe_frozen_fun_vars_list ::
  "'f muL \<Rightarrow> ('f,'v) rules \<Rightarrow> bool"
where
  "muterm_safe_frozen_fun_vars_list \<mu> R \<longleftrightarrow>
    list_all (\<lambda>(l,r). list_all (\<lambda>h. is_Fun h \<longrightarrow>
      list_all (\<lambda>x. x \<in> set (mu_vars_term_list \<mu> l))
        (mu_vars_term_list \<mu> h)) (muterm_frozen_roots_list \<mu> r)) R"

lemma muterm_safe_frozen_fun_vars_list_sound:
  assumes safe: "muterm_safe_frozen_fun_vars_list \<mu> R"
    and lr: "(l,r) \<in> set R" and frozen: "muterm_frozen_root_on (mu_of \<mu>) r h"
    and hfun: "is_Fun h"
  shows "mu_vars_term (mu_of \<mu>) h \<subseteq> mu_vars_term (mu_of \<mu>) l"
proof -
  from safe have outer: "\<forall>lr \<in> set R. case lr of (l,r) \<Rightarrow>
    list_all (\<lambda>h. is_Fun h \<longrightarrow>
      list_all (\<lambda>x. x \<in> set (mu_vars_term_list \<mu> l))
        (mu_vars_term_list \<mu> h)) (muterm_frozen_roots_list \<mu> r)"
    unfolding muterm_safe_frozen_fun_vars_list_def list_all_iff by blast
  have rule_safe: "list_all (\<lambda>h. is_Fun h \<longrightarrow>
      list_all (\<lambda>x. x \<in> set (mu_vars_term_list \<mu> l))
        (mu_vars_term_list \<mu> h)) (muterm_frozen_roots_list \<mu> r)"
  proof -
    from outer[rule_format, OF lr] show ?thesis by simp
  qed
  have hmem: "h \<in> set (muterm_frozen_roots_list \<mu> r)"
    using frozen muterm_frozen_roots_list_set by blast
  from rule_safe hmem hfun have members: "\<forall>x \<in> set (mu_vars_term_list \<mu> h).
    x \<in> set (mu_vars_term_list \<mu> l)"
    unfolding list_all_iff by blast
  show ?thesis
  proof
    fix x
    assume xh: "x \<in> mu_vars_term (mu_of \<mu>) h"
    have xhl: "x \<in> set (mu_vars_term_list \<mu> h)"
      using xh by (simp only: set_mu_vars_term_list)
    from members xhl have "x \<in> set (mu_vars_term_list \<mu> l)" by blast
    then show "x \<in> mu_vars_term (mu_of \<mu>) l"
      by (simp only: set_mu_vars_term_list)
  qed
qed


definition muterm_safe_migrating_vars_list ::
  "'f muL \<Rightarrow> ('f,'v) rules \<Rightarrow> bool"
where
  "muterm_safe_migrating_vars_list \<mu> R \<longleftrightarrow>
    list_all (\<lambda>(l,r). list_all (\<lambda>x.
      Var x \<in> set (muterm_frozen_roots_list \<mu> l))
      [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
        x \<notin> set (mu_vars_term_list \<mu> l)]) R"

lemma muterm_safe_migrating_vars_list_sound:
  assumes safe: "muterm_safe_migrating_vars_list \<mu> R"
    and lr: "(l,r) \<in> set R"
    and xr: "x \<in> mu_vars_term (mu_of \<mu>) r"
    and xl: "x \<notin> mu_vars_term (mu_of \<mu>) l"
  shows "muterm_frozen_root_on (mu_of \<mu>) l (Var x)"
proof -
  from safe have outer: "\<forall>lr \<in> set R. case lr of (l,r) \<Rightarrow>
    list_all (\<lambda>x. Var x \<in> set (muterm_frozen_roots_list \<mu> l))
      [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
        x \<notin> set (mu_vars_term_list \<mu> l)]"
    unfolding muterm_safe_migrating_vars_list_def list_all_iff by blast
  have rule_safe: "list_all (\<lambda>x.
      Var x \<in> set (muterm_frozen_roots_list \<mu> l))
      [x \<leftarrow> remdups (mu_vars_term_list \<mu> r).
        x \<notin> set (mu_vars_term_list \<mu> l)]"
  proof -
    from outer[rule_format, OF lr] show ?thesis by simp
  qed
  have xr': "x \<in> set (mu_vars_term_list \<mu> r)" using xr by simp
  have xl': "x \<notin> set (mu_vars_term_list \<mu> l)" using xl by simp
  from rule_safe xr' xl' have "Var x \<in> set (muterm_frozen_roots_list \<mu> l)"
    unfolding list_all_iff by simp
  then show ?thesis using muterm_frozen_roots_list_set by blast
qed


definition muterm_safe_frozen_vars_list ::
  "'f muL \<Rightarrow> ('f,'v) rules \<Rightarrow> bool"
where
  "muterm_safe_frozen_vars_list \<mu> R \<longleftrightarrow>
    list_all (\<lambda>(l,r). list_all (\<lambda>x.
      x \<in> set (mu_vars_term_list \<mu> l) \<or>
      Var x \<in> set (muterm_frozen_roots_list \<mu> l))
      [x \<leftarrow> remdups (vars_term_list r).
        Var x \<in> set (muterm_frozen_roots_list \<mu> r)]) R"

lemma muterm_safe_frozen_vars_list_sound:
  assumes safe: "muterm_safe_frozen_vars_list \<mu> R"
    and lr: "(l,r) \<in> set R"
    and frozen: "muterm_frozen_root_on (mu_of \<mu>) r (Var x)"
  shows "x \<in> mu_vars_term (mu_of \<mu>) l \<or>
    muterm_frozen_root_on (mu_of \<mu>) l (Var x)"
proof -
  from safe have outer: "\<forall>lr \<in> set R. case lr of (l,r) \<Rightarrow>
    list_all (\<lambda>x. x \<in> set (mu_vars_term_list \<mu> l) \<or>
      Var x \<in> set (muterm_frozen_roots_list \<mu> l))
      [x \<leftarrow> remdups (vars_term_list r).
        Var x \<in> set (muterm_frozen_roots_list \<mu> r)]"
    unfolding muterm_safe_frozen_vars_list_def list_all_iff by blast
  have rule_safe: "list_all (\<lambda>x.
      x \<in> set (mu_vars_term_list \<mu> l) \<or>
      Var x \<in> set (muterm_frozen_roots_list \<mu> l))
      [x \<leftarrow> remdups (vars_term_list r).
        Var x \<in> set (muterm_frozen_roots_list \<mu> r)]"
  proof -
    from outer[rule_format, OF lr] show ?thesis by simp
  qed
  have xr: "x \<in> set (vars_term_list r)"
  proof -
    have "r \<rhd> Var x" by (rule muterm_frozen_root_supt[OF frozen])
    then have "r \<unrhd> Var x" unfolding supt_supteq_conv by blast
    then have "x \<in> vars_term r" by (rule subteq_Var_imp_in_vars_term)
    then show ?thesis by (simp only: set_vars_term_list)
  qed
  have fr: "Var x \<in> set (muterm_frozen_roots_list \<mu> r)"
    using frozen muterm_frozen_roots_list_set by blast
  from rule_safe xr fr have result:
    "x \<in> set (mu_vars_term_list \<mu> l) \<or>
      Var x \<in> set (muterm_frozen_roots_list \<mu> l)"
    unfolding list_all_iff by simp
  show ?thesis
  proof (rule disjE[OF result])
    assume "x \<in> set (mu_vars_term_list \<mu> l)"
    then show ?thesis by (simp only: set_mu_vars_term_list, blast)
  next
    assume "Var x \<in> set (muterm_frozen_roots_list \<mu> l)"
    then show ?thesis using muterm_frozen_roots_list_set by blast
  qed
qed


definition muterm_unhiding_safe_list ::
  "'f muL \<Rightarrow> ('f,'v) rules \<Rightarrow> bool"
where
  "muterm_unhiding_safe_list \<mu> R \<longleftrightarrow>
    muterm_safe_frozen_fun_vars_list \<mu> R \<and>
    muterm_safe_migrating_vars_list \<mu> R \<and>
    muterm_safe_frozen_vars_list \<mu> R \<and>
    list_all (\<lambda>(l,r). list_all (\<lambda>h. is_Fun h \<longrightarrow>
      muterm_frozen_roots_list \<mu> h = [])
      (muterm_frozen_roots_list \<mu> r)) R"

lemma muterm_unhiding_safe_list_sound:
  assumes safe: "muterm_unhiding_safe_list \<mu> R"
  shows "muterm_unhiding_safe_on (mu_of \<mu>) (set R)"
  unfolding muterm_unhiding_safe_on_def
proof (intro conjI allI impI)
  fix l r h
  assume lr: "(l,r) \<in> set R" and frozen: "muterm_frozen_root_on (mu_of \<mu>) r h"
    and hfun: "is_Fun h"
  from safe have first: "muterm_safe_frozen_fun_vars_list \<mu> R"
    unfolding muterm_unhiding_safe_list_def by blast
  show "mu_vars_term (mu_of \<mu>) h \<subseteq> mu_vars_term (mu_of \<mu>) l"
    by (rule muterm_safe_frozen_fun_vars_list_sound[OF first lr frozen hfun])
next
  fix l r x
  assume lr: "(l,r) \<in> set R" and xr: "x \<in> mu_vars_term (mu_of \<mu>) r"
    and xl: "x \<notin> mu_vars_term (mu_of \<mu>) l"
  from safe have second: "muterm_safe_migrating_vars_list \<mu> R"
    unfolding muterm_unhiding_safe_list_def by blast
  show "muterm_frozen_root_on (mu_of \<mu>) l (Var x)"
    by (rule muterm_safe_migrating_vars_list_sound[OF second lr xr xl])
next
  fix l r x
  assume lr: "(l,r) \<in> set R"
    and frozen: "muterm_frozen_root_on (mu_of \<mu>) r (Var x)"
  from safe have third: "muterm_safe_frozen_vars_list \<mu> R"
    unfolding muterm_unhiding_safe_list_def by blast
  show "x \<in> mu_vars_term (mu_of \<mu>) l \<or>
    muterm_frozen_root_on (mu_of \<mu>) l (Var x)"
    by (rule muterm_safe_frozen_vars_list_sound[OF third lr frozen])
next
  fix l r h s
  assume lr: "(l,r) \<in> set R" and frozen: "muterm_frozen_root_on (mu_of \<mu>) r h"
    and hfun: "is_Fun h"
  from safe have flat: "list_all (\<lambda>(l,r). list_all (\<lambda>h. is_Fun h \<longrightarrow>
      muterm_frozen_roots_list \<mu> h = [])
      (muterm_frozen_roots_list \<mu> r)) R"
    unfolding muterm_unhiding_safe_list_def by blast
  from flat have outer: "\<forall>lr \<in> set R. case lr of (l,r) \<Rightarrow>
    list_all (\<lambda>h. is_Fun h \<longrightarrow> muterm_frozen_roots_list \<mu> h = [])
      (muterm_frozen_roots_list \<mu> r)"
    unfolding list_all_iff by blast
  from flat lr have rule_flat: "list_all (\<lambda>h. is_Fun h \<longrightarrow>
      muterm_frozen_roots_list \<mu> h = [])
      (muterm_frozen_roots_list \<mu> r)"
  proof -
    from outer[rule_format, OF lr] show ?thesis by simp
  qed
  have hmem: "h \<in> set (muterm_frozen_roots_list \<mu> r)"
    using frozen muterm_frozen_roots_list_set by blast
  from rule_flat hmem hfun have "muterm_frozen_roots_list \<mu> h = []"
    unfolding list_all_iff by blast
  then have empty: "set (muterm_frozen_roots_list \<mu> h) = {}" by simp
  show "\<not> muterm_frozen_root_on (mu_of \<mu>) h s"
  proof
    assume frozen': "muterm_frozen_root_on (mu_of \<mu>) h s"
    have "s \<in> set (muterm_frozen_roots_list \<mu> h)"
      using frozen' muterm_frozen_roots_list_set by blast
    with empty show False by simp
  qed
qed


lemma muterm_exact_list_coverage:
  fixes R P U :: "('f::{showl,compare_order},string) rules"
    and D :: "('f \<times> nat) list" and \<mu> :: "'f muL" and shp :: "'f \<Rightarrow> 'f"
  assumes mu_pairs: "set (mu_CSDP_list shp R \<mu> D) \<subseteq> set P"
    and collapsing: "set (csr_rta08_collapsing_CSDP_list shp \<mu> R) \<subseteq> set P"
    and exact: "set (muterm_exact_unhiding_rules_list shp \<mu> D R) \<subseteq> set U"
    and safe: "muterm_unhiding_safe_list \<mu> R"
  shows "muterm_unhiding_coverage shp (mu_of \<mu>) (set D)
    (set R) (set P) (set U)"
proof -
  have mu_cover: "mu_CSDP_on shp (mu_of \<mu>) (set D) (set R) \<subseteq> set P"
    using mu_pairs CSR_Checker_Base.mu_CSDP_list[of shp R \<mu> D] by simp
  have collapsing_cover:
    "csr_rta08_collapsing_CSDP_on shp (mu_of \<mu>) (set R) \<subseteq> set P"
    using collapsing unfolding csr_rta08_collapsing_CSDP_list by simp
  have exact_cover: "\<And>h t. (\<exists>l r. (l,r) \<in> set R \<and>
      muterm_frozen_root_on (mu_of \<mu>) r h) \<Longrightarrow>
      muterm_active_defined_call_on (mu_of \<mu>) (set D) h t \<Longrightarrow>
      (h,sharp_term shp t) \<in> set U"
    using exact unfolding muterm_exact_unhiding_rules_list_set by blast
  have safe_sem: "muterm_unhiding_safe_on (mu_of \<mu>) (set R)"
    by (rule muterm_unhiding_safe_list_sound[OF safe])
  show ?thesis unfolding muterm_unhiding_coverage_def
    using mu_cover collapsing_cover safe_sem exact_cover by blast
qed

declare muterm_frozen_roots_list.simps[simp del]
declare muterm_active_defined_calls_list.simps[simp del]

(*
definition innermost_unhiding_projection_rules_list ::
  "'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, string) rules"
where
  "innermost_unhiding_projection_rules_list \<mu> F =
    concat (map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun f xs, xs ! i))
        [i \<leftarrow> [0..<n]. i \<in> mu_of \<mu> (f,n)]) F)"

definition innermost_unhiding_marking_pairs_list ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow>
    ('f,'v) rules \<Rightarrow> ('f,'v) rules"
where
  "innermost_unhiding_marking_pairs_list shp \<mu> D R =
    concat (map (\<lambda>(l,r). map (\<lambda>p. (r |_ p, sharp_term shp (r |_ p)))
      [p \<leftarrow> fun_poss_list r.
        p \<notin> set (mu_fun_poss_list \<mu> r) \<and>
        root (r |_ p) \<in> Some ` set D]) R)"

lemma innermost_unhiding_marking_pairs_list:
  "set (innermost_unhiding_marking_pairs_list shp \<mu> D R) =
    {(h,sharp_term shp h) |h. hidden_term_on (mu_of \<mu>) (set D) (set R) h}"
  unfolding innermost_unhiding_marking_pairs_list_def hidden_term_on_def
    inactive_fun_subterm_on_def
  by (auto simp: set_concat split: term.splits prod.splits)

lemma innermost_unhiding_projection_rules_list_step:
  assumes fn: "(f,n) \<in> set F"
    and len: "length ts = n"
    and i: "i < n" "i \<in> mu_of \<mu> (f,n)"
  shows "(Fun f ts, ts ! i)
    \<in> rstep (set (innermost_unhiding_projection_rules_list \<mu> F))"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?xs = "map Var ?vs"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs" by simp_all
  have inst: "map (\<lambda>t. t \<cdot> ?\<sigma>) ?xs = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len by simp
  have ilen: "i < length ?xs" using i fresh by simp
  have nth_inst: "?xs ! i \<cdot> ?\<sigma> = ts ! i"
    using arg_cong[OF inst, of "\<lambda>xs. xs ! i"] ilen by simp
  let ?rs = "map (\<lambda>i. (Fun f ?xs, ?xs ! i))
    [i \<leftarrow> [0..<n]. i \<in> mu_of \<mu> (f,n)]"
  have rs_mem: "?rs \<in> set (map (\<lambda>(f,n).
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun f xs, xs ! i))
        [i \<leftarrow> [0..<n]. i \<in> mu_of \<mu> (f,n)]) F)"
    unfolding set_map
  proof (rule image_eqI[of _ _ "(f,n)"])
    show "?rs = (case (f,n) of (f,n) \<Rightarrow>
      let xs = map Var (x\<^sub>1_to_x\<^sub>n n)
      in map (\<lambda>i. (Fun f xs, xs ! i))
        [i \<leftarrow> [0..<n]. i \<in> mu_of \<mu> (f,n)])"
      by (simp only: Let_def case_prod_conv)
    show "(f,n) \<in> set F" by (rule fn)
  qed
  have pair_mem: "(Fun f ?xs, ?xs ! i) \<in> set ?rs" using i by simp
  have rule: "(Fun f ?xs, ?xs ! i) \<in>
      set (innermost_unhiding_projection_rules_list \<mu> F)"
    unfolding innermost_unhiding_projection_rules_list_def
    using rs_mem pair_mem by (simp only: set_concat, blast)
  show ?thesis
  proof (rule rstepI[OF rule, where C = \<box> and \<sigma> = ?\<sigma>])
    show "Fun f ts = \<box>\<langle>Fun f ?xs \<cdot> ?\<sigma>\<rangle>" using inst by simp
    show "ts ! i = \<box>\<langle>?xs ! i \<cdot> ?\<sigma>\<rangle>" using nth_inst by simp
  qed
qed

lemma innermost_unhiding_list_coverage:
  fixes R P S :: "('f::{showl,compare_order},string) rules"
    and D F :: "('f \<times> nat) list" and \<mu> :: "'f muL" and shp :: "'f \<Rightarrow> 'f"
  assumes mu_pairs: "set (mu_CSDP_list shp R \<mu> D) \<subseteq> set P"
    and collapsing: "set (csr_rta08_collapsing_CSDP_list shp \<mu> R) \<subseteq> set P"
    and projections: "set (innermost_unhiding_projection_rules_list \<mu> F) \<subseteq> set S"
    and markings: "set (innermost_unhiding_marking_pairs_list shp \<mu> D R) \<subseteq> set P"
    and RF: "set (funas_trs_list R) \<subseteq> set F"
  shows "innermost_unhiding_csdp_coverage shp (mu_of \<mu>) (set D)
    (set R) (set P) (set S)"
proof -
  have mu_cover: "mu_CSDP_on shp (mu_of \<mu>) (set D) (set R) \<subseteq> set P"
    using mu_pairs CSR_Checker_Base.mu_CSDP_list[of shp R \<mu> D] by simp
  have collapsing_cover:
    "csr_rta08_collapsing_CSDP_on shp (mu_of \<mu>) (set R) \<subseteq> set P"
    using collapsing unfolding csr_rta08_collapsing_CSDP_list by simp
  have projection_cover: "\<And>f ts i.
      hides_position_on (mu_of \<mu>) (set D) (set R) (f,length ts) i \<Longrightarrow>
      i < length ts \<Longrightarrow> (Fun f ts, ts ! i) \<in> rstep (set S)"
  proof -
    fix f :: 'f and ts :: "('f,string) term list" and i
    assume hide: "hides_position_on (mu_of \<mu>) (set D) (set R)
      (f,length ts) i" and pos: "i < length ts"
    from hide obtain l r p us where lr: "(l,r) \<in> set R"
      and p: "p \<in> fun_poss r" and sub: "r |_ p = Fun f us"
      and lens: "length us = length ts"
      and active: "i \<in> mu_of \<mu> (f,length ts)"
      unfolding hides_position_on_def by auto
    have sub_funas: "funas_term (r |_ p) \<subseteq> funas_term r"
      by (meson fun_poss_imp_poss p subt_at_imp_supteq' supteq_imp_funas_term_subset)
    have root_mem: "(f,length ts) \<in> funas_term (r |_ p)"
      unfolding sub using lens by simp
    have rhs_mem: "(f,length ts) \<in> funas_term r" using sub_funas root_mem by blast
    have fn: "(f,length ts) \<in> set (funas_trs_list R)"
      using lr rhs_mem by (force simp: funas_trs_def funas_rule_def)
    have fnF: "(f,length ts) \<in> set F" using RF fn by blast
    have base: "(Fun f ts, ts ! i) \<in> rstep
      (set (innermost_unhiding_projection_rules_list \<mu> F))"
      by (rule innermost_unhiding_projection_rules_list_step[OF fnF refl pos active])
    show "(Fun f ts, ts ! i) \<in> rstep (set S)"
      using base rstep_mono[OF projections] by blast
  qed
  have marking_cover: "\<And>h. hidden_term_on (mu_of \<mu>) (set D) (set R) h
      \<Longrightarrow> (h, sharp_term shp h) \<in> set P"
    using markings unfolding innermost_unhiding_marking_pairs_list by blast
  show ?thesis unfolding innermost_unhiding_csdp_coverage_def
    using mu_cover collapsing_cover projection_cover marking_cover by blast
qed
*)

end
