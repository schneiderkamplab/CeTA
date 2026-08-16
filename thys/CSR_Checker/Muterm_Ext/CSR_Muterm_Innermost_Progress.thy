theory CSR_Muterm_Innermost_Progress
  imports CSR_Muterm_Innermost_Usable_Exec
begin

lemma innermost_mu_Tinf_defined_root:
  fixes R :: "('f::{showl,compare_order},'v) trs"
    and t :: "('f,'v) term"
  assumes wf: "wf_trs R"
    and T: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  obtains f ts where "t = Fun f ts" and "defined R (f,length ts)"
proof -
  from mu_Tinf_innermost_imp_first_root_step[
    where t=t and \<mu>=\<mu> and R=R, OF T]
  obtain s u where pref: "(t,s) \<in> (innermost_csnrstep \<mu> R)\<^sup>*"
    and root: "(s,u) \<in> innermost_csrstep \<mu> R" by blast
  have pref_full: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    by (rule rtrancl_mono[OF innermost_csnrstep_subset_csnrstep,
      THEN subsetD, OF pref])
  from innermost_csrstep_subset_csrstep[THEN subsetD, OF root]
  obtain l r \<sigma> where lr: "(l,r) \<in> R" and s: "s = l \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain f ls where l: "l = Fun f ls"
    unfolding wf_trs_def by (cases l, auto)
  have root_s: "root s = Some (f,length ls)" unfolding s l by simp
  have root_t: "root t = Some (f,length ls)"
    using csnrsteps_preserve_root[OF pref_full] root_s by simp
  obtain g ts where t: "t = Fun g ts" using root_t by (cases t, auto)
  from root_t have g: "g = f" and len: "length ts = length ls"
    unfolding t by auto
  have def: "defined R (g,length ts)"
    unfolding defined_def
  proof (intro exI conjI)
    show "(l,r) \<in> R" by (rule lr)
    show "root l = Some (g,length ts)" unfolding l using g len by simp
  qed
  show ?thesis by (rule that[OF t def])
qed

lemma muterm_new_frozen_fun_unhide_finite_innermost:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and lr: "(l,r) \<in> R" and lhs: "is_Fun l"
    and source_finite: "\<And>x q. x \<in> mu_vars_term \<mu> l \<Longrightarrow>
      q \<in> mu_fun_poss \<mu> (\<sigma> x) \<Longrightarrow>
      SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q}"
    and frozen: "muterm_frozen_root_on \<mu> r h" and hfun: "is_Fun h"
    and active: "h \<cdot> \<sigma> = t \<or> mu_supt \<mu> (h \<cdot> \<sigma>) t"
    and tT: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  shows "(h \<cdot> \<sigma>,sharp_term shp t) \<in> rrstep U"
proof -
  from innermost_mu_Tinf_defined_root[OF wf tT]
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
    have subfun: "is_Fun (h |_ p)" unfolding base by simp
    have rhs: "sharp_term shp t = sharp_term shp (h |_ p) \<cdot> \<sigma>"
      unfolding inst by (simp add: sharp_term_subst_distr_2[OF subfun])
    show ?thesis unfolding rrstep_def' using rule rhs by blast
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
    have sn: "SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q2}"
      by (rule source_finite[OF xl q2])
    moreover from tT have
      "\<not> SN_on (innermost_csstep \<mu> R) {t}"
      unfolding mu_Tinf_def by auto
    ultimately show ?thesis unfolding ti by contradiction
  qed
qed

lemma innermost_csrstep_muterm_unhiding_preserve_finite:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and step: "(u,v) \<in> innermost_csrstep \<mu> R"
    and source_finite: "\<And>x q l r \<sigma>. (l,r) \<in> R \<Longrightarrow>
      u = l \<cdot> \<sigma> \<Longrightarrow> x \<in> mu_vars_term \<mu> l \<Longrightarrow>
      q \<in> mu_fun_poss \<mu> (\<sigma> x) \<Longrightarrow>
      SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q}"
    and unhidable:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U u"
  shows "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U v"
proof -
  from innermost_csrstep_subset_csrstep[THEN subsetD, OF step]
  obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and u: "u = l \<cdot> \<sigma>" and v: "v = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l" unfolding wf_trs_def by (cases l, auto)
  show ?thesis unfolding is_muterm_unhidable_def
  proof (intro allI impI)
    fix s t
    assume component: "muterm_frozen_component_on \<mu> v s"
      and active: "s = t \<or> mu_supt \<mu> s t"
      and tT: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    show "(s,sharp_term shp t) \<in> rrstep U"
    apply (rule muterm_rhs_component_cases[
      OF cover lr lhs component[unfolded v]])
    proof -
      fix h
      assume new1: "muterm_frozen_root_on \<mu> r h" and new2: "is_Fun h"
        and new3: "s = h \<cdot> \<sigma>"
      show ?thesis unfolding new3
        by (rule muterm_new_frozen_fun_unhide_finite_innermost[
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
      from innermost_mu_Tinf_defined_root[OF wf tT]
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
        have at': "\<sigma> x |_ (i # qs) = t" using sat active_var2 by simp
        show thesis by (rule that[OF q' at'])
      qed
      have sn: "SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q}"
        by (rule source_finite[OF lr u active_var1 q])
      moreover from tT have "\<not> SN_on (innermost_csstep \<mu> R) {t}"
        unfolding mu_Tinf_def by auto
      ultimately show ?thesis unfolding at by contradiction
    qed
  qed
qed

lemma innermost_SN_on_active_subst_mu_subterm:
  assumes wf: "wf_trs R" and lhs: "is_Fun l"
    and source: "SN_on (innermost_csstep \<mu> R) {l \<cdot> \<sigma>}"
    and x: "x \<in> mu_vars_term \<mu> l"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q}"
proof -
  from x obtain p where p: "p \<in> mu_poss \<mu> l" and lp: "l |_ p = Var x"
    unfolding mu_vars_term_def by auto
  have pq: "p @ q \<in> mu_fun_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_subst_var_lift[
      where t=l and x=x and \<sigma>=\<sigma>, OF p lp q])
  have pos: "p @ q \<in> mu_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_imp_mu_poss[OF pq])
  have sub: "(l \<cdot> \<sigma>) |_ (p @ q) = \<sigma> x |_ q"
    using mu_poss_imp_poss[OF p] lp by (simp add: subt_at_append)
  from SN_on_innermost_csstep_mu_pos[OF wf pos source]
  show ?thesis unfolding sub .
qed

lemma innermost_csstep_muterm_unhiding_preserve_guarded:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and step: "(u,v) \<in> innermost_csstep \<mu> R"
    and guard: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<or>
      SN_on (innermost_csstep \<mu> R) {u}"
    and unhidable:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U u"
  shows "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U v"
  using step guard unhidable
proof (induct u arbitrary: v)
  case (Var x)
  have "(Var x,v) \<in> csstep \<mu> R"
    using Var.prems(1) innermost_csstep_subset_csstep by blast
  from csstep_Var_empty_wf[OF wf, of x v \<mu>] this
  show ?case by contradiction
next
  case (Fun f ss)
  show ?case
  proof (cases "(Fun f ss,v) \<in> innermost_csrstep \<mu> R")
    case True
    have finite: "\<And>x q l r \<sigma>. (l,r) \<in> R \<Longrightarrow>
      Fun f ss = l \<cdot> \<sigma> \<Longrightarrow> x \<in> mu_vars_term \<mu> l \<Longrightarrow>
      q \<in> mu_fun_poss \<mu> (\<sigma> x) \<Longrightarrow>
      SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q}"
    proof -
      fix x q l r \<sigma>
      assume lr: "(l,r) \<in> R" and src: "Fun f ss = l \<cdot> \<sigma>"
        and x: "x \<in> mu_vars_term \<mu> l"
        and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
      from wf lr have lhs: "is_Fun l" unfolding wf_trs_def by (cases l, auto)
      show "SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q}"
      proof (rule disjE[OF Fun.prems(2)])
        assume T: "Fun f ss \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
        show ?thesis by (rule innermost_mu_Tinf_SN_on_active_subst_mu_subterm[
          OF lhs T[unfolded src] x q])
      next
        assume SN: "SN_on (innermost_csstep \<mu> R) {Fun f ss}"
        show ?thesis by (rule innermost_SN_on_active_subst_mu_subterm[
          OF wf lhs SN[unfolded src] x q])
      qed
    qed
    show ?thesis
    proof (rule innermost_csrstep_muterm_unhiding_preserve_finite)
      show "wf_trs R" by (rule wf)
      show "{g. defined R g} \<subseteq> D" by (rule defs)
      show "muterm_unhiding_coverage shp \<mu> D R P U" by (rule cover)
      show "(Fun f ss,v) \<in> innermost_csrstep \<mu> R" by (rule True)
      show "\<And>x q l r \<sigma>. (l,r) \<in> R \<Longrightarrow>
          Fun f ss = l \<cdot> \<sigma> \<Longrightarrow> x \<in> mu_vars_term \<mu> l \<Longrightarrow>
          q \<in> mu_fun_poss \<mu> (\<sigma> x) \<Longrightarrow>
          SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q}"
        by (rule finite)
      show "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U
          (Fun f ss)" by (rule Fun.prems(3))
    qed
  next
    case False
    with Fun.prems(1) have nonroot:
      "(Fun f ss,v) \<in> innermost_csnrstep \<mu> R"
      unfolding innermost_csstep_root_nonroot by blast
    from innermost_csnrstep_FunE[OF nonroot]
    obtain i ts where i: "i < length ss" "i \<in> \<mu> (f,length ss)"
      and v: "v = Fun f ts" and len: "length ts = length ss"
      and child_step: "(ss ! i,ts ! i) \<in> innermost_csstep \<mu> R"
      and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
        ts ! j = ss ! j" by blast
    have child_full: "(ss ! i,ts ! i) \<in> csstep \<mu> R"
      using child_step innermost_csstep_subset_csstep by blast
    from child_full have child_fun: "is_Fun (ss ! i)"
      by (cases "ss ! i", use csstep_Var_empty_wf[OF wf] in auto)
    have child_SN: "SN_on (innermost_csstep \<mu> R) {ss ! i}"
    proof (rule disjE[OF Fun.prems(2)])
      assume T: "Fun f ss \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      have sub: "mu_supt \<mu> (Fun f ss) (ss ! i)"
        unfolding mu_supt_def using i child_fun
        by (intro exI[of _ i] exI[of _ "[]"], cases "ss ! i", auto)
      show ?thesis using T sub unfolding mu_Tinf_def by blast
    next
      assume SN: "SN_on (innermost_csstep \<mu> R) {Fun f ss}"
      have pos: "[i] \<in> mu_poss \<mu> (Fun f ss)"
        using i child_fun by (cases "ss ! i", auto)
      from SN_on_innermost_csstep_mu_pos[OF wf pos SN]
      show ?thesis using i by simp
    qed
    have child_unhidable:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U (ss ! i)"
    proof (rule muterm_unhidable_active_subterm[OF Fun.prems(3)])
      show "Fun f ss = ss ! i \<or> mu_supt \<mu> (Fun f ss) (ss ! i)"
        unfolding mu_supt_def using i child_fun
        by (intro disjI2 exI[of _ i] exI[of _ "[]"], cases "ss ! i", auto)
    qed
    have changed_unhidable:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U (ts ! i)"
      by (rule Fun.hyps[OF nth_mem[OF i(1)] child_step disjI2[OF child_SN]
        child_unhidable])
    show ?thesis unfolding v is_muterm_unhidable_def
    proof (intro allI impI)
      fix s t
      assume component: "muterm_frozen_component_on \<mu> (Fun f ts) s"
        and active: "s = t \<or> mu_supt \<mu> s t"
        and tT: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      from component[unfolded muterm_frozen_component_on_Fun]
      show "(s,sharp_term shp t) \<in> rrstep U"
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
            show "j \<in> \<mu> (f,length ss)" using j(2) len by simp
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
        have frozen_child: "muterm_frozen_root_on \<mu> (Fun f ss) (ss ! j)"
          unfolding muterm_frozen_root_on_Fun
          by (intro disjI1 exI[of _ j] conjI,
              rule js, use j(2) len in simp, rule refl)
        have old: "muterm_frozen_component_on \<mu> (Fun f ss) s"
        proof (rule_tac P = "s = ts ! j" and
            Q = "muterm_frozen_component_on \<mu> (ts ! j) s" in HOL.disjE)
          show "s = ts ! j \<or> muterm_frozen_component_on \<mu> (ts ! j) s"
            by (rule comp)
        next
          assume eq: "s = ts ! j"
          have root_s: "muterm_frozen_root_on \<mu> (Fun f ss) s"
            using frozen_child eq replace by simp
          show ?thesis by (rule muterm_frozen_component_on.direct[OF root_s])
        next
          assume child: "muterm_frozen_component_on \<mu> (ts ! j) s"
          have child': "muterm_frozen_component_on \<mu> (ss ! j) s"
            using child replace by simp
          show ?thesis by (rule muterm_frozen_component_on.nested[
            OF frozen_child child'])
        qed
        from Fun.prems(3) old active tT show ?thesis
          unfolding is_muterm_unhidable_def by blast
      qed
    qed
  qed
qed

lemma innermost_muterm_unhiding_preserving_steps:
  assumes wf: "wf_trs R" and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and steps: "(u,v) \<in> (innermost_csnrstep \<mu> R)\<^sup>*"
    and hp: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U u"
    and vT: "v \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  shows "has_muterm_unhiding_property shp \<mu>
    (innermost_csstep \<mu> R) U v"
  using steps hp vT
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have yz: "(y,z) \<in> innermost_csstep \<mu> R"
    using step.hyps(2) unfolding innermost_csstep_root_nonroot by auto
  from step.prems(2) have notSN_z:
      "\<not> SN_on (innermost_csstep \<mu> R) {z}"
    unfolding mu_Tinf_def by auto
  have notSN_y: "\<not> SN_on (innermost_csstep \<mu> R) {y}"
    by (rule step_notSN_on_source[OF yz notSN_z])
  from step.prems(1) have uT:
      "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  have yT: "y \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    by (rule innermost_csnrsteps_mu_Tinf_preserve[
      OF wf step.hyps(1) uT notSN_y])
  have hp_y: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U y"
    by (rule step.hyps(3)[OF step.prems(1) yT])
  from hp_y have unhidable_y:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U y"
    unfolding has_muterm_unhiding_property_def by auto
  have unhidable_z:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U z"
    by (rule innermost_csstep_muterm_unhiding_preserve_guarded[
      OF wf defs cover yz disjI1[OF yT] unhidable_y])
  show ?case unfolding has_muterm_unhiding_property_def
    using step.prems(2) unhidable_z by blast
qed

lemma innermost_csrstep_muterm_unhiding_progress:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
    and R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and root: "(s,v) \<in> innermost_csrstep \<mu> R"
    and hp: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U s"
    and notSN: "\<not> SN_on (innermost_csstep \<mu> R) {v}"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
  shows "\<exists>u. has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U u \<and>
    (sharp_term shp s,sharp_term shp u) \<in>
      muterm_innermost_typed_pair_step shp \<mu> R P U"
proof -
  from root obtain lr \<sigma> where rewrite:
      "(s,v) \<in> rstep_r_p_s R lr [] \<sigma>"
    and inner0: "\<And>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    unfolding innermost_csrstep_def innermost_csstep_p_def by blast
  obtain l r where lr_def: "lr = (l,r)" by (cases lr)
  from rewrite have lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and v: "v = r \<cdot> \<sigma>"
    unfolding lr_def rstep_r_p_s_def' by auto
  have inner: "\<And>u. mu_supt \<mu> (l \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    using inner0 unfolding lr_def by simp
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  have source: "innermost_pair_source shp \<mu> R
      (sharp_term shp (l \<cdot> \<sigma>))"
    unfolding innermost_pair_source_def
    using lr lhs inner by blast
  have source_s: "innermost_pair_source shp \<mu> R (sharp_term shp s)"
    using source unfolding s .
  from hp have sT: "s \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and unhidable_s:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U s"
    unfolding has_muterm_unhiding_property_def by auto
  have unhidable_v:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U v"
  proof (rule innermost_csrstep_muterm_unhiding_preserve_finite[
      OF wf defs cover root _ unhidable_s])
    fix x q l' r' \<tau>
    assume lr': "(l',r') \<in> R" and src: "s = l' \<cdot> \<tau>"
      and x: "x \<in> mu_vars_term \<mu> l'"
      and q: "q \<in> mu_fun_poss \<mu> (\<tau> x)"
    from wf lr' have lhs': "is_Fun l'"
      unfolding wf_trs_def by (cases l', auto)
    show "SN_on (innermost_csstep \<mu> R) {\<tau> x |_ q}"
      by (rule innermost_mu_Tinf_SN_on_active_subst_mu_subterm[
        OF lhs' sT[unfolded src] x q])
  qed
  from innermost_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded v]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f,length us)"
    and uT: "(r \<cdot> \<sigma>) |_ p \<in>
      mu_Tinf \<mu> (innermost_csstep \<mu> R)"
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
  have unhidable_u:
      "is_muterm_unhidable shp \<mu> (innermost_csstep \<mu> R) U ?u"
    by (rule muterm_unhidable_active_subterm[OF unhidable_v active_u])
  have hp_u: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U ?u"
    unfolding has_muterm_unhiding_property_def using uT unhidable_u by blast
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  have typed: "(sharp_term shp s,sharp_term shp ?u) \<in>
      muterm_innermost_typed_pair_step shp \<mu> R P U"
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "?u = (r |_ p) \<cdot> \<sigma>" by auto
    from mu_fun_poss_imp_fun_poss[OF p_r]
    obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
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
      with sT have "SN_on (innermost_csstep \<mu> R)
          {(r |_ p) \<cdot> \<sigma>}"
        unfolding s mu_Tinf_def by blast
      moreover from uT have "\<not> SN_on (innermost_csstep \<mu> R) {?u}"
        unfolding mu_Tinf_def by auto
      ultimately show False unfolding sub_subst by contradiction
    qed
    have pair0: "(sharp_term shp l,sharp_term shp (r |_ p))
        \<in> mu_CSDP_on shp \<mu> D R"
      unfolding CSR_Checker_Base.mu_CSDP_on_def
      using lr p_r rp fD ns by blast
    have pair: "(sharp_term shp l,sharp_term shp (r |_ p)) \<in> P"
      using pair0 muterm_unhiding_coverage_mu[OF cover] by blast
    have noncoll: "muterm_noncollapsing_rrstep P
        (sharp_term shp s) (sharp_term shp ?u)"
      unfolding muterm_noncollapsing_rrstep_def s sub_subst
      by (intro exI[of _ "sharp_term shp l"]
          exI[of _ "sharp_term shp (r |_ p)"] exI[of _ \<sigma>],
          use pair rp lhs in auto)
    show ?thesis
      unfolding muterm_innermost_typed_pair_step_def
        muterm_typed_pair_step_def
      apply (rule IntI)
      apply (rule UnI1)
      apply (rule Quasi_Order.mem_rel_ofI)
      apply (rule noncoll)
      apply (rule Quasi_Order.mem_rel_ofI)
      apply (rule source_s)
      done
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> ?u = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and u: "?u = \<sigma> x |_ q2" by blast
    have xr: "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    have xl: "x \<notin> mu_vars_term \<mu> l"
    proof
      assume xl: "x \<in> mu_vars_term \<mu> l"
      have "SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q2}"
        by (rule innermost_mu_Tinf_SN_on_active_subst_mu_subterm[
          OF lhs sT[unfolded s] xl q2])
      moreover from uT have "\<not> SN_on (innermost_csstep \<mu> R) {?u}"
        unfolding mu_Tinf_def by auto
      ultimately show False unfolding u by contradiction
    qed
    have frozen_l: "muterm_frozen_root_on \<mu> l (Var x)"
      by (rule muterm_unhiding_safe_migrating[OF cover lr xr xl])
    have frozen_inst: "muterm_frozen_root_on \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
      using muterm_frozen_root_subst[OF frozen_l, of \<sigma>] by simp
    have frozen_component:
        "muterm_frozen_component_on \<mu> (l \<cdot> \<sigma>) (\<sigma> x)"
      by (rule muterm_frozen_component_on.direct[OF frozen_inst])
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
    have unhide: "(\<sigma> x,sharp_term shp ?u) \<in> rrstep U"
      using unhidable_s frozen_component active_xu uT unfolding s
        is_muterm_unhidable_def by blast
    have collapse: "muterm_collapsing_rrstep P
        (sharp_term shp s) (\<sigma> x)"
      unfolding s
      by (rule muterm_collapsing_instance_typed[OF cover lr xr xl lhs])
    show ?thesis
      unfolding muterm_innermost_typed_pair_step_def
        muterm_typed_pair_step_def
      apply (rule IntI)
      apply (rule UnI2)
      apply (rule Quasi_Order.mem_rel_ofI)
      apply (intro exI conjI)
      apply (rule collapse)
      apply (rule unhide)
      apply (rule Quasi_Order.mem_rel_ofI)
      apply (rule source_s)
      done
  qed
  show ?thesis using hp_u typed by blast
qed

lemma innermost_muterm_unhiding_relstep:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
    and R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and hp: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
  shows "\<exists>u. has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U u \<and>
    (sharp_term shp t,sharp_term shp u) \<in>
      (innermost_csdp_step shp \<mu> R)\<^sup>* O
      muterm_innermost_typed_pair_step shp \<mu> R P U O
      (innermost_csdp_step shp \<mu> R)\<^sup>*"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  from mu_Tinf_innermost_imp_first_root_step[OF Tinf]
  obtain s v where pref: "(t,s) \<in> (innermost_csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> innermost_csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (innermost_csstep \<mu> R) {v}"
    by blast
  have sv: "(s,v) \<in> innermost_csstep \<mu> R"
    using root unfolding innermost_csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (innermost_csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    by (rule innermost_csnrsteps_mu_Tinf_preserve[
      OF wf pref Tinf notSN_s])
  have hp_s: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U s"
    by (rule innermost_muterm_unhiding_preserving_steps[
      OF wf defs cover pref hp sT])
  from innermost_csrstep_muterm_unhiding_progress[
      OF wf root hp_s notSN_v defs cover]
  obtain u where hp_u: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U u"
    and pair: "(sharp_term shp s,sharp_term shp u) \<in>
      muterm_innermost_typed_pair_step shp \<mu> R P U"
    by blast
  have left: "(sharp_term shp t,sharp_term shp s) \<in>
      (innermost_csdp_step shp \<mu> R)\<^sup>*"
    by (rule innermost_csnrsteps_imp_sharp_innermost_csdp_steps[OF pref])
  have right: "(sharp_term shp u,sharp_term shp u) \<in>
      (innermost_csdp_step shp \<mu> R)\<^sup>*" by simp
  show ?thesis using hp_u left pair right by blast
qed

theorem finite_muterm_innermost_typed_dpp_imp_SN_innermost:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
    and R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and fin: "finite_muterm_innermost_typed_dpp shp \<mu> R P U"
  shows "SN (innermost_csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (innermost_csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN]
  obtain t0 where t0T: "t0 \<in> Tinf (innermost_csstep \<mu> R)" by blast
  have hp0: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  let ?S = "innermost_csdp_step shp \<mu> R"
  let ?Q = "muterm_innermost_typed_pair_step shp \<mu> R P U"
  let ?A = "?S\<^sup>* O ?Q O ?S\<^sup>*"
  have step_ex: "\<And>t. has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U t \<Longrightarrow>
    \<exists>u. has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U u \<and>
      (sharp_term shp t,sharp_term shp u) \<in> ?A"
    by (rule innermost_muterm_unhiding_relstep[OF wf _ defs cover])
  have all_ex: "\<forall>t. \<exists>u. has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U t \<longrightarrow>
    has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U u \<and>
      (sharp_term shp t,sharp_term shp u) \<in> ?A"
    using step_ex by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U t \<Longrightarrow>
    has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U (nxt t) \<and>
      (sharp_term shp t,sharp_term shp (nxt t)) \<in> ?A"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_hp: "has_muterm_unhiding_property shp \<mu>
      (innermost_csstep \<mu> R) U (ts n)" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] show ?case unfolding ts_def by simp
  qed
  have ts_step: "(sharp_term shp (ts n),sharp_term shp (ts (Suc n)))
      \<in> ?A" for n
    using nxt[OF ts_hp[of n]] unfolding ts_def by simp
  define f where "f n = sharp_term shp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?A"
    unfolding f_def using ts_step by simp
  have "\<not> SN ?A" unfolding SN_defs using chain by blast
  moreover from fin have "SN_rel ?Q ?S"
    unfolding finite_muterm_innermost_typed_dpp_def .
  then have "SN ?A" unfolding SN_rel_on_def .
  ultimately show False by contradiction
qed

lemma finite_muterm_expanded_imp_finite_innermost_typed:
  assumes fin: "finite_mode_csr_dpp shp CSR_Innermost \<mu>
      (muterm_expanded_pairs ren P U) R"
  shows "finite_muterm_innermost_typed_dpp shp \<mu> R P U"
proof -
  have pair_sub: "muterm_innermost_typed_pair_step shp \<mu> R P U \<subseteq>
      innermost_rrstep shp \<mu> R (muterm_expanded_pairs ren P U)"
    unfolding muterm_innermost_typed_pair_step_def innermost_rrstep_def
    using muterm_typed_pair_step_subset_expanded[of P U ren] by blast
  from fin have expanded: "SN_rel
      (innermost_rrstep shp \<mu> R (muterm_expanded_pairs ren P U))
      (innermost_csdp_step shp \<mu> R)"
    unfolding finite_mode_csr_dpp_def by simp
  show ?thesis unfolding finite_muterm_innermost_typed_dpp_def
    by (rule SN_rel_mono[OF pair_sub subset_refl expanded])
qed

theorem muterm_expanded_innermost_imp_SN_csstep_without_rhs_condition:
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
    and R :: "('f,string) trs"
  assumes overlay: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage shp \<mu> D R P U"
    and fin: "finite_mode_csr_dpp shp CSR_Innermost \<mu>
      (muterm_expanded_pairs ren P U) R"
  shows "SN (csstep \<mu> R)"
proof (rule csr_switch_overlay_innermost_termination[OF overlay wf])
  have typed: "finite_muterm_innermost_typed_dpp shp \<mu> R P U"
    by (rule finite_muterm_expanded_imp_finite_innermost_typed[OF fin])
  show "SN (innermost_csstep \<mu> R)"
    by (rule finite_muterm_innermost_typed_dpp_imp_SN_innermost[
      OF wf defs cover typed])
qed

theorem muterm_expanded_innermost_usable_imp_SN_csstep:
  fixes R U P S :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),string) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes overlay: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and closed: "muterm_innermost_ur_closed R U \<mu> (P \<union> S)"
    and conservative: "rhs_mu_vars_condition \<mu> U"
    and target: "muterm_innermost_typed_target_safe R U \<mu> P S"
    and fin: "finite_dpp (False,False,
      muterm_expanded_pairs ren P S,{},{},{},U)"
  shows "SN (csstep \<mu> R)"
proof (rule csr_switch_overlay_innermost_termination[OF overlay wf])
  have typed: "finite_muterm_innermost_typed_dpp Sharp \<mu> R P S"
    by (rule finite_muterm_innermost_typed_dpp_expanded_usable[
      OF wf fresh closed conservative target fin])
  show "SN (innermost_csstep \<mu> R)"
    by (rule finite_muterm_innermost_typed_dpp_imp_SN_innermost[
      OF wf defs cover typed])
qed

end
