theory Outermost_Signature_Extension
  imports
    Outermost_RZ_Transformation
    TRS.Signature_Extension
begin

fun foreign_depth :: "'f sig \<Rightarrow> ('f,'v) term \<Rightarrow> nat" where
  "foreign_depth F (Var x) = 0"
| "foreign_depth F (Fun f ts) =
    Max (insert 0 (foreign_depth F ` set ts)) +
      (if (f,length ts) \<in> F then 0 else 1)"

definition list_singleton_ext :: "'a rel \<Rightarrow> 'a list rel" where
  "list_singleton_ext R =
    {(xs @ a # ys, xs @ b # ys) | xs a ys b. (a,b) \<in> R}"

definition multiset_singleton_ext_outer :: "'a rel \<Rightarrow> 'a multiset rel" where
  "multiset_singleton_ext_outer R =
    {({#a#} + A, {#b#} + A) | a A b. (a,b) \<in> R}"

lemma multiset_singleton_ext_outer_mult1:
  "multiset_singleton_ext_outer R \<subseteq> (mult1 (R\<inverse>))\<inverse>"
  unfolding multiset_singleton_ext_outer_def
  by (auto, metis add_mset_add_single converseI mult1_singleton mult1_union)

lemma multiset_singleton_ext_outer_mult:
  "multiset_singleton_ext_outer R \<subseteq> (mult (R\<inverse>))\<inverse>"
  using multiset_singleton_ext_outer_mult1[of R]
  using mult_def r_into_trancl' by blast

lemma SN_multiset_singleton_ext_outer:
  assumes "SN R"
  shows "SN (multiset_singleton_ext_outer R)"
proof (rule SN_subset[OF _ multiset_singleton_ext_outer_mult])
  from assms show "SN ((mult (R\<inverse>))\<inverse>)"
    unfolding SN_iff_wf converse_converse by (rule wf_mult)
qed

lemma list_singleton_ext_mset:
  "list_singleton_ext R \<subseteq>
    inv_image (multiset_singleton_ext_outer R) mset"
proof (intro subsetI)
  fix z
  assume "z \<in> list_singleton_ext R"
  then obtain xs a ys b where z: "z = (xs @ a # ys, xs @ b # ys)"
    and ab: "(a,b) \<in> R" unfolding list_singleton_ext_def by blast
  have left: "mset (xs @ a # ys) = {#a#} + (mset xs + mset ys)"
    by (simp add: ac_simps)
  have right: "mset (xs @ b # ys) = {#b#} + (mset xs + mset ys)"
    by (simp add: ac_simps)
  have ms: "(mset (xs @ a # ys), mset (xs @ b # ys)) \<in>
      multiset_singleton_ext_outer R"
    unfolding left right multiset_singleton_ext_outer_def using ab by blast
  show "z \<in> inv_image (multiset_singleton_ext_outer R) mset"
    unfolding z inv_image_def using ms by simp
qed

lemma SN_list_singleton_ext:
  assumes "SN R"
  shows "SN (list_singleton_ext R)"
  by (rule SN_subset[OF SN_inv_image[OF
        SN_multiset_singleton_ext_outer[OF assms]] list_singleton_ext_mset])

lemma foreign_depth_arg_le:
  assumes "u \<in> set ts"
  shows "foreign_depth F u \<le> foreign_depth F (Fun f ts)"
proof -
  have finite: "finite (insert 0 (foreign_depth F ` set ts))" by simp
  have member: "foreign_depth F u \<in>
      insert 0 (foreign_depth F ` set ts)" using assms by auto
  from Max_ge[OF finite member] show ?thesis by simp
qed

lemma foreign_depth_arg_less_if_foreign:
  assumes "u \<in> set ts" and "(f,length ts) \<notin> F"
  shows "foreign_depth F u < foreign_depth F (Fun f ts)"
proof -
  have finite: "finite (insert 0 (foreign_depth F ` set ts))" by simp
  have member: "foreign_depth F u \<in>
      insert 0 (foreign_depth F ` set ts)" using assms(1) by auto
  from Max_ge[OF finite member] assms(2) show ?thesis by simp
qed

lemma foreign_depth_subterm_le:
  assumes "p \<in> poss t"
  shows "foreign_depth F (t |_ p) \<le> foreign_depth F t"
  using assms
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts"
    and pp: "p \<in> poss (ts ! i)" by (cases t, auto)
  from Cons.hyps[OF pp] foreign_depth_arg_le[of "ts ! i" ts F f]
  show ?case unfolding t using i by auto
qed

lemma foreign_depth_alien_le:
  assumes "a \<in> set (aliens F t)"
  shows "foreign_depth F a \<le> foreign_depth F t"
proof -
  from supteq_imp_subt_at[OF aliens_imp_supteq[OF assms]]
  obtain p where p: "p \<in> poss t" and at: "t |_ p = a" by blast
  show ?thesis unfolding at[symmetric] by (rule foreign_depth_subterm_le[OF p])
qed

lemma ostep_subset_rstep: "ostep Q R \<subseteq> rstep R"
  unfolding ostep_def ostep_p_def
  by (auto dest: rstep_r_p_s_imp_rstep)

lemma foreign_depth_subst_var_le:
  assumes x: "x \<in> vars_term t" and sig: "funas_term t \<subseteq> F"
  shows "foreign_depth F (\<sigma> x) \<le> foreign_depth F (t \<cdot> \<sigma>)"
  using x sig
proof (induct t)
  case (Var y)
  then show ?case by simp
next
  case (Fun f ts)
  from Fun.prems(1) obtain u where u: "u \<in> set ts" and x: "x \<in> vars_term u"
    by auto
  from Fun.prems(2) u have usig: "funas_term u \<subseteq> F" by auto
  from Fun.hyps[OF u x usig]
  have le_u: "foreign_depth F (\<sigma> x) \<le> foreign_depth F (u \<cdot> \<sigma>)" .
  have member: "u \<cdot> \<sigma> \<in> set (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
    using u by auto
  from le_u foreign_depth_arg_le[OF member, of F f]
  show ?case by simp
qed

lemma foreign_depth_subst_mono:
  assumes tsig: "funas_term t \<subseteq> F"
    and usig: "funas_term u \<subseteq> F"
    and vars: "vars_term u \<subseteq> vars_term t"
  shows "foreign_depth F (u \<cdot> \<sigma>) \<le> foreign_depth F (t \<cdot> \<sigma>)"
  using usig vars
proof (induct u)
  case (Var x)
  then show ?case using foreign_depth_subst_var_le[OF _ tsig, of x \<sigma>] by simp
next
  case (Fun f us)
  have fF: "(f,length us) \<in> F" using Fun.prems(1) by simp
  have each: "\<And>v. v \<in> set us \<Longrightarrow>
      foreign_depth F (v \<cdot> \<sigma>) \<le> foreign_depth F (t \<cdot> \<sigma>)"
  proof -
    fix v
    assume v: "v \<in> set us"
    from Fun.hyps[OF v] Fun.prems v
    show "foreign_depth F (v \<cdot> \<sigma>) \<le> foreign_depth F (t \<cdot> \<sigma>)"
      by auto
  qed
  have finite: "finite (insert 0
      (foreign_depth F ` set (map (\<lambda>v. v \<cdot> \<sigma>) us)))" by simp
  have bound: "\<And>n. n \<in> insert 0
      (foreign_depth F ` set (map (\<lambda>v. v \<cdot> \<sigma>) us)) \<Longrightarrow>
      n \<le> foreign_depth F (t \<cdot> \<sigma>)"
    using each by auto
  have max_le: "Max (insert 0
      (foreign_depth F ` set (map (\<lambda>v. v \<cdot> \<sigma>) us)))
      \<le> foreign_depth F (t \<cdot> \<sigma>)"
    using finite bound by (simp add: Max_le_iff)
  from max_le fF show ?case by simp
qed

lemma foreign_depth_Fun_update_le:
  assumes i: "i < length ts"
    and le: "foreign_depth F u \<le> foreign_depth F (ts ! i)"
  shows "foreign_depth F (Fun f (ts[i := u])) \<le>
    foreign_depth F (Fun f ts)"
proof -
  let ?S = "insert 0 (foreign_depth F ` set ts)"
  let ?U = "insert 0 (foreign_depth F ` set (ts[i := u]))"
  have finite: "finite ?S" by simp
  have bound: "\<And>n. n \<in> ?U \<Longrightarrow> n \<le> Max ?S"
  proof -
    fix n
    assume n: "n \<in> ?U"
    show "n \<le> Max ?S"
    proof (cases "n = 0")
      case True
      have "0 \<in> ?S" by simp
      from Max_ge[OF finite this] True show ?thesis by simp
    next
      case False
      from n False obtain x where x: "x \<in> set (ts[i := u])"
        and n: "n = foreign_depth F x" by auto
      show ?thesis
      proof (cases "foreign_depth F x = foreign_depth F u")
        case True
        have old: "foreign_depth F (ts ! i) \<in> ?S" using i by auto
        from le Max_ge[OF finite old] True n show ?thesis by simp
      next
        case xu: False
        from x obtain j where j: "j < length (ts[i := u])"
          and xj: "x = (ts[i := u]) ! j" unfolding set_conv_nth by blast
        have ji: "j \<noteq> i"
        proof
          assume "j = i"
          with i j xj xu show False by simp
        qed
        from i j have jold: "j < length ts" by simp
        from xj ji i jold have "x = ts ! j" by simp
        with jold n have "n \<in> ?S" by auto
        from Max_ge[OF finite this] show ?thesis .
      qed
    qed
  qed
  have max_le: "Max ?U \<le> Max ?S"
    by (simp add: Max_le_iff bound)
  have len: "length (ts[i := u]) = length ts" by simp
  show ?thesis unfolding foreign_depth.simps len using max_le by simp
qed

lemma foreign_depth_replace_at_le:
  assumes p: "p \<in> poss t"
    and le: "foreign_depth F u \<le> foreign_depth F (t |_ p)"
  shows "foreign_depth F (replace_at t p u) \<le> foreign_depth F t"
  using p le
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts"
    and pp: "p \<in> poss (ts ! i)" by (cases t, auto)
  from Cons.prems(2) t i
  have le_local: "foreign_depth F u \<le> foreign_depth F (ts ! i |_ p)" by simp
  from Cons.hyps[OF pp le_local]
  have local: "foreign_depth F (replace_at (ts ! i) p u) \<le>
      foreign_depth F (ts ! i)" by simp
  from foreign_depth_Fun_update_le[OF i local]
  have updated: "foreign_depth F (Fun f
      (ts[i := replace_at (ts ! i) p u])) \<le> foreign_depth F (Fun f ts)" .
  have rep: "replace_at (Fun f ts) (i # p) u =
      Fun f (ts[i := replace_at (ts ! i) p u])"
    using i by (simp add: upd_conv_take_nth_drop)
  show ?case unfolding t rep using updated .
qed

lemma foreign_depth_rstep_le:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R" and sig: "funas_trs R \<subseteq> F"
    and step: "(s,t) \<in> rstep R"
  shows "foreign_depth F t \<le> foreign_depth F s"
proof -
  from step[unfolded rstep_iff_rstep_r_p_s]
  obtain p lr \<sigma> where raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    by blast
  from raw have p: "p \<in> poss s" and lr: "lr \<in> R"
    and at: "s |_ p = fst lr \<cdot> \<sigma>"
    and t: "t = replace_at s p (snd lr \<cdot> \<sigma>)"
    unfolding rstep_r_p_s_def' by auto
  from lr sig have lhs: "funas_term (fst lr) \<subseteq> F"
    and rhs: "funas_term (snd lr) \<subseteq> F"
    unfolding funas_trs_def funas_rule_def by auto
  from wf lr have vars: "vars_term (snd lr) \<subseteq> vars_term (fst lr)"
    unfolding wf_trs_def by auto
  from foreign_depth_subst_mono[OF lhs rhs vars, of \<sigma>]
  have local: "foreign_depth F (snd lr \<cdot> \<sigma>) \<le>
      foreign_depth F (s |_ p)" unfolding at .
  from foreign_depth_replace_at_le[OF p local]
  show ?thesis unfolding t .
qed

context cleaning_same_var
begin

lemma clean_term_subterm_weak_match:
  assumes p: "p \<in> poss (clean_term t)"
  shows "p \<in> poss t \<and> weak_match (t |_ p) (clean_term t |_ p)"
  using p
proof (induct p arbitrary: t)
  case Nil
  then show ?case using clean_weak_match by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  have f: "(f,length ts) \<in> F"
  proof (rule ccontr)
    assume "(f,length ts) \<notin> F"
    then have "clean_term (Fun f ts) = const" using const by simp
    with Cons.prems t var show False by (cases const, auto)
  qed
  with Cons.prems t obtain i: "i < length ts"
    and pp: "p \<in> poss (clean_term (ts ! i))" by auto
  from Cons(1)[OF pp] i t f show ?case by auto
qed

lemma quasi_left_linear_clean_match_imp_match:
  assumes quasi: "quasi_left_linear_lhss Q"
    and l: "l \<in> Q"
    and p: "p \<in> poss (clean_term t)"
    and matched: "clean_term t |_ p = l \<cdot> \<sigma>"
  shows "\<exists>k\<in>Q. \<exists>\<tau>. t |_ p = k \<cdot> \<tau>"
proof -
  from quasi l obtain k \<rho> where k: "k \<in> Q"
    and linear: "linear_term k" and inst: "k \<cdot> \<rho> = l"
    unfolding quasi_left_linear_lhss_def by blast
  from clean_term_subterm_weak_match[OF p]
  have weak: "weak_match (t |_ p) (clean_term t |_ p)" by blast
  have "clean_term t |_ p = k \<cdot> (\<rho> \<circ>\<^sub>s \<sigma>)"
    using matched inst by (simp add: subst_subst)
  from linear_weak_match[OF linear weak this]
  obtain \<tau> where "t |_ p = k \<cdot> \<tau>" by blast
  with k show ?thesis by blast
qed

lemma quasi_left_linear_clean_ostep_cond:
  assumes quasi: "quasi_left_linear_lhss Q"
    and p: "p \<in> poss (clean_term t)"
    and cond: "ostep_cond Q p t"
  shows "ostep_cond Q p (clean_term t)"
  unfolding ostep_cond_def ostep_cond_single_def
proof (intro ballI allI impI notI)
  fix l q
  assume l: "l \<in> Q" and qp: "q <\<^sub>p p"
    and redex: "\<exists>\<sigma>. clean_term t |_ q = l \<cdot> \<sigma>"
  from qp p have q: "q \<in> poss (clean_term t)"
    unfolding less_pos_def' using poss_append_poss by blast
  from redex obtain \<sigma> where match: "clean_term t |_ q = l \<cdot> \<sigma>"
    by blast
  from quasi_left_linear_clean_match_imp_match[OF quasi l q match]
  obtain k \<tau> where k: "k \<in> Q" and match': "t |_ q = k \<cdot> \<tau>"
    by blast
  from clean_term_subterm_weak_match[OF p] have pt: "p \<in> poss t" by blast
  from qp pt have qt: "q \<in> poss t"
    unfolding less_pos_def' using poss_append_poss by blast
  from cond[unfolded ostep_cond_def ostep_cond_single_def,
      rule_format, OF k qp]
  show False using match' by blast
qed

lemma clean_rstep_r_p_s:
  fixes R :: "('f,'v) trs"
  assumes raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and sig: "funas_trs R \<subseteq> F"
    and pclean: "p \<in> poss (clean_term s)"
  shows "(clean_term s, clean_term t) \<in>
    rstep_r_p_s R lr p (clean_subst \<sigma>)"
  using raw pclean
proof (induct p arbitrary: s t)
  case Nil
  from Nil.prems(1) have lr: "lr \<in> R"
    and s: "s = fst lr \<cdot> \<sigma>" and t: "t = snd lr \<cdot> \<sigma>"
    unfolding rstep_r_p_s_def' by auto
  from lr sig have lhs: "funas_term (fst lr) \<subseteq> F"
    and rhs: "funas_term (snd lr) \<subseteq> F"
    unfolding funas_trs_def funas_rule_def by auto
  show ?case unfolding s t rstep_r_p_s_def'
    by (simp add: lr clean_subst_apply_term[OF lhs]
        clean_subst_apply_term[OF rhs])
next
  case (Cons i q)
  show ?case
  proof (cases s)
    case (Var x)
    with Cons.prems(1) show ?thesis unfolding rstep_r_p_s_def' by auto
  next
    case (Fun f ss)
    from Cons.prems(1)[unfolded Fun rstep_r_p_s_def' Cons]
    have i: "i < length ss" and q: "q \<in> poss (ss ! i)"
      and lr: "lr \<in> R" and at: "ss ! i |_ q = fst lr \<cdot> \<sigma>"
      and t: "t = Fun f (ss[i := replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)])"
      by (auto simp: upd_conv_take_nth_drop)
    let ?u = "replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)"
    have local_raw: "(ss ! i, ?u) \<in> rstep_r_p_s R lr q \<sigma>"
      unfolding rstep_r_p_s_def' using q lr at by auto
    have fF: "(f,length ss) \<in> F"
    proof (rule ccontr)
      assume "(f,length ss) \<notin> F"
      then have "clean_term (Fun f ss) = const" using const by simp
      with Cons.prems(2)[unfolded Fun] var show False by (cases const, auto)
    qed
    from Cons.prems(2)[unfolded Fun] fF i
    have qclean: "q \<in> poss (clean_term (ss ! i))" by simp
    from Cons.hyps[OF local_raw qclean]
    have local: "(clean_term (ss ! i), clean_term ?u) \<in>
        rstep_r_p_s R lr q (clean_subst \<sigma>)" .
    from local i fF show ?thesis
      unfolding Fun t rstep_r_p_s_def'
      by (auto simp: map_update nth_map upd_conv_take_nth_drop take_map drop_map)
  qed
qed

lemma clean_ostep_if_position_survives:
  fixes R :: "('f,'v) trs"
  assumes quasi: "quasi_left_linear_lhss Q"
    and sig: "funas_trs R \<subseteq> F"
    and step: "(s,t) \<in> ostep Q R"
    and pclean: "p \<in> poss (clean_term s)"
    and at_p: "(s,t) \<in> ostep_p Q R p"
  shows "(clean_term s, clean_term t) \<in> ostep Q R"
proof -
  from at_p obtain lr \<sigma> where raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "ostep_cond Q p s" by auto
  have raw_clean: "(clean_term s, clean_term t) \<in>
      rstep_r_p_s R lr p (clean_subst \<sigma>)"
    by (rule clean_rstep_r_p_s[OF raw sig pclean])
  have cond_clean: "ostep_cond Q p (clean_term s)"
    by (rule quasi_left_linear_clean_ostep_cond[OF quasi pclean cond])
  show ?thesis unfolding ostep_def
    using ostep_pI[OF raw_clean cond_clean] by blast
qed

lemma clean_rstep_erased:
  fixes R :: "('f,'v) trs"
  assumes raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and erased: "p \<notin> poss (clean_term s)"
  shows "clean_term s = clean_term t"
  using raw erased
proof (induct p arbitrary: s t)
  case Nil
  then show ?case by simp
next
  case (Cons i q)
  show ?case
  proof (cases s)
    case (Var x)
    with Cons.prems(1) show ?thesis unfolding rstep_r_p_s_def' by auto
  next
    case (Fun f ss)
    from Cons.prems(1)[unfolded Fun rstep_r_p_s_def' Cons]
    have i: "i < length ss" and q: "q \<in> poss (ss ! i)"
      and lr: "lr \<in> R" and at: "ss ! i |_ q = fst lr \<cdot> \<sigma>"
      and t: "t = Fun f (ss[i := replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)])"
      by (auto simp: upd_conv_take_nth_drop)
    let ?u = "replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)"
    have local_raw: "(ss ! i, ?u) \<in> rstep_r_p_s R lr q \<sigma>"
      unfolding rstep_r_p_s_def' using q lr at by auto
    show ?thesis
    proof (cases "(f,length ss) \<in> F")
      case False
      have left: "clean_term (Fun f ss) = const" using False const by simp
      have len: "length (ss[i := ?u]) = length ss" by simp
      have right: "clean_term (Fun f (ss[i := ?u])) = const"
        using False len const by simp
      show ?thesis unfolding Fun t left right ..
    next
      case True
      from Cons.prems(2)[unfolded Fun] True i
      have erased_local: "q \<notin> poss (clean_term (ss ! i))" by simp
      from Cons.hyps[OF local_raw erased_local]
      have eq: "clean_term (ss ! i) = clean_term ?u" .
      have val_eq: "clean_term ?u = map clean_term ss ! i"
        using i eq by simp
      have update: "(map clean_term ss)[i := clean_term ?u] = map clean_term ss"
        unfolding val_eq by (rule list_update_id)
      show ?thesis unfolding Fun t using True i update
        by (simp add: map_update)
    qed
  qed
qed

lemma ostep_cond_child:
  assumes i: "i < length ss"
    and cond: "ostep_cond Q (i # p) (Fun f ss)"
  shows "ostep_cond Q p (ss ! i)"
  unfolding ostep_cond_def ostep_cond_single_def
proof (intro ballI allI impI notI)
  fix l q
  assume l: "l \<in> Q" and qp: "q <\<^sub>p p"
    and redex: "\<exists>\<sigma>. ss ! i |_ q = l \<cdot> \<sigma>"
  have iqip: "i # q <\<^sub>p i # p" using qp
    unfolding less_pos_def' by auto
  from cond have cond': "\<forall>l\<in>Q. \<forall>q. q <\<^sub>p i # p \<longrightarrow>
      \<not> (\<exists>\<sigma>. Fun f ss |_ q = l \<cdot> \<sigma>)"
    unfolding ostep_cond_def ostep_cond_single_def .
  from cond'[rule_format, OF l iqip] i redex show False by auto
qed

lemma ostep_foreign_root_update:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R" and sig: "funas_trs R \<subseteq> F"
    and foreign: "(f,length ss) \<notin> F"
    and step: "(Fun f ss,t) \<in> ostep Q R"
  shows "\<exists>i u. i < length ss \<and>
    t = Fun f (ss[i := u]) \<and> (ss ! i,u) \<in> ostep Q R"
proof -
  from step obtain p where at_p: "(Fun f ss,t) \<in> ostep_p Q R p"
    unfolding ostep_def by blast
  from at_p obtain lr \<sigma> where
    raw: "(Fun f ss,t) \<in> rstep_r_p_s R lr p \<sigma>" and
    cond: "ostep_cond Q p (Fun f ss)" by auto
  show ?thesis
  proof (cases p)
    case Nil
    from raw[unfolded Nil rstep_r_p_s_def']
    have lr: "lr \<in> R" and root: "Fun f ss = fst lr \<cdot> \<sigma>" by auto
    have "\<exists>g ls. fst lr = Fun g ls"
      using wf lr unfolding wf_trs_def by (cases lr, auto)
    then obtain g ls where lhs: "fst lr = Fun g ls" by blast
    from root[unfolded lhs] have g: "g = f" and len: "length ls = length ss"
      by auto
    from lr sig have lhs_sig: "funas_term (fst lr) \<subseteq> F"
      unfolding funas_trs_def funas_rule_def by auto
    from lhs_sig have root_F: "(g,length ls) \<in> F" unfolding lhs by simp
    from root_F foreign g len show ?thesis by simp
  next
    case (Cons i q)
    from raw[unfolded Cons rstep_r_p_s_def']
    have i: "i < length ss" and q: "q \<in> poss (ss ! i)"
      and lr: "lr \<in> R" and at: "ss ! i |_ q = fst lr \<cdot> \<sigma>"
      and t: "t = Fun f (ss[i := replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)])"
      by (auto simp: upd_conv_take_nth_drop)
    let ?u = "replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)"
    have local_raw: "(ss ! i,?u) \<in> rstep_r_p_s R lr q \<sigma>"
      unfolding rstep_r_p_s_def' using q lr at by auto
    have local_cond: "ostep_cond Q q (ss ! i)"
      by (rule ostep_cond_child[OF i cond[unfolded Cons]])
    have local: "(ss ! i,?u) \<in> ostep Q R"
      unfolding ostep_def using ostep_pI[OF local_raw local_cond] by blast
    show ?thesis using i t local by blast
  qed
qed

lemma SN_on_ostep_foreign_root:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R" and sig: "funas_trs R \<subseteq> F"
    and foreign: "(f,length ss) \<notin> F"
    and args_SN: "\<And>u. u \<in> set ss \<Longrightarrow> SN_on (ostep Q R) {u}"
  shows "SN_on (ostep Q R) {Fun f ss}"
proof
  fix seq
  assume start: "seq 0 \<in> {Fun f ss}" and chain: "chain (ostep Q R) seq"
  let ?O = "ostep Q R"
  have shape_SN: "\<exists>us. seq i = Fun f us \<and> length us = length ss \<and>
      (\<forall>u\<in>set us. SN_on ?O {u})" for i
  proof (induct i)
    case 0
    show ?case using start args_SN by auto
  next
    case (Suc i)
    from Suc obtain us where si: "seq i = Fun f us"
      and len: "length us = length ss"
      and sn: "\<forall>u\<in>set us. SN_on ?O {u}" by blast
    from chain[rule_format, of i] have step: "(Fun f us,seq (Suc i)) \<in> ?O"
      unfolding si .
    have foreign_us: "(f,length us) \<notin> F" using foreign len by simp
    from ostep_foreign_root_update[OF wf sig foreign_us step]
    obtain j v where j: "j < length us"
      and target: "seq (Suc i) = Fun f (us[j := v])"
      and local: "(us ! j,v) \<in> ?O" by blast
    have sn_v: "SN_on ?O {v}"
      by (rule step_preserves_SN_on[OF local sn[rule_format]])
         (use j in auto)
    have all: "\<forall>u\<in>set (us[j := v]). SN_on ?O {u}"
    proof (intro ballI)
      fix u
      assume u: "u \<in> set (us[j := v])"
      from set_update_subset_insert[of us j v, THEN subsetD, OF u]
      show "SN_on ?O {u}" using sn sn_v by auto
    qed
    show ?case using target len all by auto
  qed
  let ?as = "\<lambda>i. args (seq i)"
  have list_chain: "chain (list_singleton_ext (restrict_SN ?O ?O)) ?as"
  proof
    fix i
    from shape_SN[of i] obtain us where si: "seq i = Fun f us"
      and len: "length us = length ss"
      and sn: "\<forall>u\<in>set us. SN_on ?O {u}" by blast
    from chain[rule_format, of i] have step: "(Fun f us,seq (Suc i)) \<in> ?O"
      unfolding si .
    have foreign_us: "(f,length us) \<notin> F" using foreign len by simp
    from ostep_foreign_root_update[OF wf sig foreign_us step]
    obtain j v where j: "j < length us"
      and target: "seq (Suc i) = Fun f (us[j := v])"
      and local: "(us ! j,v) \<in> ?O" by blast
    have restricted: "(us ! j,v) \<in> restrict_SN ?O ?O"
      unfolding restrict_SN_def using local sn j by auto
    have us: "us = take j us @ us ! j # drop (Suc j) us"
      using j by (metis id_take_nth_drop)
    have upd: "us[j := v] = take j us @ v # drop (Suc j) us"
      using j by (simp add: upd_conv_take_nth_drop)
    have ext: "(us,us[j := v]) \<in>
        list_singleton_ext (restrict_SN ?O ?O)"
      unfolding list_singleton_ext_def using restricted us upd by blast
    have asi: "?as i = us" unfolding si by simp
    have assuc: "?as (Suc i) = us[j := v]" unfolding target by simp
    show "(?as i,?as (Suc i)) \<in>
        list_singleton_ext (restrict_SN ?O ?O)"
      unfolding asi assuc using ext .
  qed
  have list_SN: "SN (list_singleton_ext (restrict_SN ?O ?O))"
    by (rule SN_list_singleton_ext, simp)
  have witness: "?as 0 \<in> UNIV \<and>
      chain (list_singleton_ext (restrict_SN ?O ?O)) ?as"
    using list_chain by simp
  have exists_chain: "\<exists>g. g 0 \<in> UNIV \<and>
      chain (list_singleton_ext (restrict_SN ?O ?O)) g"
    by (rule exI[of _ ?as], rule witness)
  from list_SN exists_chain show False unfolding SN_defs by contradiction
qed

lemma erased_ostep_updates_one_alien:
  fixes R :: "('f,'v) trs"
  assumes raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "ostep_cond Q p s"
    and erased: "p \<notin> poss (clean_term s)"
  shows "\<exists>xs a b ys. aliens F s = xs @ a # ys \<and>
    aliens F t = xs @ b # ys \<and> (a,b) \<in> ostep Q R"
  using raw cond erased
proof (induct p arbitrary: s t)
  case Nil
  then show ?case by simp
next
  case (Cons i q)
  show ?case
  proof (cases s)
    case (Var x)
    with Cons.prems(1) show ?thesis unfolding rstep_r_p_s_def' by auto
  next
    case (Fun f ss)
    from Cons.prems(1)[unfolded Fun rstep_r_p_s_def' Cons]
    have i: "i < length ss" and q: "q \<in> poss (ss ! i)"
      and lr: "lr \<in> R" and at: "ss ! i |_ q = fst lr \<cdot> \<sigma>"
      and t: "t = Fun f (ss[i := replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)])"
      by (auto simp: upd_conv_take_nth_drop)
    let ?u = "replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)"
    have local_raw: "(ss ! i, ?u) \<in> rstep_r_p_s R lr q \<sigma>"
      unfolding rstep_r_p_s_def' using q lr at by auto
    show ?thesis
    proof (cases "(f,length ss) \<in> F")
      case False
      have as: "aliens F (Fun f ss) = [Fun f ss]" using False by simp
      have len: "length (ss[i := ?u]) = length ss" by simp
      have alt_root: "aliens F (Fun f (ss[i := ?u])) = [Fun f (ss[i := ?u])]"
        using False len by simp
      have raw_parent: "(Fun f ss, Fun f (ss[i := ?u])) \<in>
          rstep_r_p_s R lr (i # q) \<sigma>"
        unfolding rstep_r_p_s_def' using i q lr at
        by (auto simp: upd_conv_take_nth_drop)
      have cond_parent: "ostep_cond Q (i # q) (Fun f ss)"
        using Cons.prems(2) unfolding Fun .
      have outer: "(Fun f ss, Fun f (ss[i := ?u])) \<in> ostep Q R"
        unfolding ostep_def using ostep_pI[OF raw_parent cond_parent]
        by blast
      show ?thesis unfolding Fun t as alt_root using outer by blast
    next
      case True
      from Cons.prems(3)[unfolded Fun] True i
      have erased_local: "q \<notin> poss (clean_term (ss ! i))" by simp
      have cond_local: "ostep_cond Q q (ss ! i)"
        by (rule ostep_cond_child[OF i Cons.prems(2)[unfolded Fun]])
      from Cons.hyps[OF local_raw cond_local erased_local]
      obtain xs a b ys where
        left: "aliens F (ss ! i) = xs @ a # ys" and
        right: "aliens F ?u = xs @ b # ys" and
        outer: "(a,b) \<in> ostep Q R" by blast
      let ?pre = "concat (map (aliens F) (take i ss))"
      let ?post = "concat (map (aliens F) (drop (Suc i) ss))"
      have ss: "ss = take i ss @ ss ! i # drop (Suc i) ss"
        using i by (metis id_take_nth_drop)
      have upd: "ss[i := ?u] = take i ss @ ?u # drop (Suc i) ss"
        using i by (simp add: upd_conv_take_nth_drop)
      have root_s: "aliens F (Fun f ss) = concat (map (aliens F) ss)"
        using True by simp
      have root_t: "aliens F (Fun f (ss[i := ?u])) =
          concat (map (aliens F) (ss[i := ?u]))"
        using True by simp
      have dec_s: "concat (map (aliens F) ss) =
          ?pre @ aliens F (ss ! i) @ ?post"
        by (subst ss, simp)
      have dec_t: "concat (map (aliens F) (ss[i := ?u])) =
          ?pre @ aliens F ?u @ ?post"
        by (subst upd, simp)
      have als: "aliens F (Fun f ss) =
          (?pre @ xs) @ a # (ys @ ?post)"
        unfolding root_s dec_s left by simp
      have alt: "aliens F (Fun f (ss[i := ?u])) =
          (?pre @ xs) @ b # (ys @ ?post)"
        unfolding root_t dec_t right by simp
      show ?thesis unfolding Fun t als alt using outer by blast
    qed
  qed
qed

lemma quasi_left_linear_clean_ostep_or_id:
  fixes R :: "('f,'v) trs"
  assumes quasi: "quasi_left_linear_lhss Q"
    and sig: "funas_trs R \<subseteq> F"
    and step: "(s,t) \<in> ostep Q R"
  shows "(clean_term s, clean_term t) \<in>
      sig_step F (ostep Q R) \<union> Id"
proof -
  from step obtain p where at_p: "(s,t) \<in> ostep_p Q R p"
    unfolding ostep_def by blast
  from at_p obtain lr \<sigma> where raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    by auto
  show ?thesis
  proof (cases "p \<in> poss (clean_term s)")
    case True
    from clean_ostep_if_position_survives[OF quasi sig step True at_p]
    have outer: "(clean_term s, clean_term t) \<in> ostep Q R" .
    have fs: "funas_term (clean_term s) \<subseteq> F"
      and ft: "funas_term (clean_term t) \<subseteq> F"
      by (rule funas_term_clean_term)+
    from sig_stepI[OF outer fs ft] show ?thesis by blast
  next
    case False
    from clean_rstep_erased[OF raw False] show ?thesis by simp
  qed
qed

theorem SN_sig_ostep_imp_SN_ostep:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R" and sig: "funas_trs R \<subseteq> F"
    and quasi: "quasi_left_linear_lhss Q"
    and source_SN: "SN (sig_step F (ostep Q R))"
  shows "SN (ostep Q R)"
proof (unfold SN_def, intro allI)
  fix t
  let ?O = "ostep Q R"
  let ?S = "sig_step F ?O"
  show "SN_on ?O {t}"
  proof (induct "foreign_depth F t" arbitrary: t rule: less_induct)
    case less
    let ?d = "foreign_depth F t"
    have alien_SN: "foreign_depth F u \<le> ?d \<Longrightarrow>
        a \<in> set (aliens F u) \<Longrightarrow> SN_on ?O {a}" for u a
    proof -
      assume ud: "foreign_depth F u \<le> ?d"
        and alien: "a \<in> set (aliens F u)"
      from aliens_root[OF alien] obtain f as where a: "a = Fun f as"
        and foreign: "(f,length as) \<notin> F"
        by (cases a, auto)
      have ad: "foreign_depth F a \<le> ?d"
        using foreign_depth_alien_le[OF alien] ud by arith
      have arg_SN: "SN_on ?O {v}" if v: "v \<in> set as" for v
      proof -
        have vd_a: "foreign_depth F v < foreign_depth F a"
          unfolding a by (rule foreign_depth_arg_less_if_foreign[OF v foreign])
        have vd: "foreign_depth F v < ?d" using vd_a ad by arith
        show ?thesis by (rule less.hyps[OF vd])
      qed
      show ?thesis unfolding a
        by (rule SN_on_ostep_foreign_root[OF wf sig foreign arg_SN])
    qed
    show ?case
    proof
      fix seq
      assume start: "seq 0 \<in> {t}" and chain: "chain ?O seq"
      let ?clean = "\<lambda>i. clean_term (seq i)"
      have clean_chain: "chain (Id \<union> ?S) ?clean"
      proof
        fix i
        from quasi_left_linear_clean_ostep_or_id[OF quasi sig
            chain[rule_format, of i]]
        show "(?clean i,?clean (Suc i)) \<in> Id \<union> ?S" by auto
      qed
      have compat: "Id O ?S \<subseteq> ?S" by auto
      have clean_start_SN: "SN_on ?S {?clean 0}"
        by (rule SN_on_subset2[OF _ source_SN], auto)
      from non_strict_ending[of ?clean Id ?S,
          OF clean_chain compat clean_start_SN]
      obtain j where stable: "\<And>i. i \<ge> j \<Longrightarrow>
          (?clean i,?clean (Suc i)) \<in> Id - ?S" by blast
      have depth: "foreign_depth F (seq i) \<le> ?d" for i
      proof (induct i)
        case 0
        show ?case using start by simp
      next
        case (Suc i)
        have rs: "(seq i,seq (Suc i)) \<in> rstep R"
          using chain[rule_format, of i] ostep_subset_rstep by blast
        from foreign_depth_rstep_le[OF wf sig rs] Suc show ?case by arith
      qed
      let ?as = "\<lambda>i. aliens F (seq (j+i))"
      have alien_chain:
        "chain (list_singleton_ext (restrict_SN ?O ?O)) ?as"
      proof
        fix i
        let ?k = "j+i"
        have step: "(seq ?k,seq (Suc ?k)) \<in> ?O"
          by (rule chain[rule_format])
        from step obtain p where at_p: "(seq ?k,seq (Suc ?k)) \<in>
            ostep_p Q R p" unfolding ostep_def by blast
        from at_p obtain lr \<sigma> where raw: "(seq ?k,seq (Suc ?k)) \<in>
            rstep_r_p_s R lr p \<sigma>" and cond: "ostep_cond Q p (seq ?k)"
          by auto
        have erased: "p \<notin> poss (clean_term (seq ?k))"
        proof
          assume survives: "p \<in> poss (clean_term (seq ?k))"
          from clean_ostep_if_position_survives[OF quasi sig step survives at_p]
          have strict: "(?clean ?k,?clean (Suc ?k)) \<in> ?O" .
          have fs: "funas_term (?clean ?k) \<subseteq> F"
            and ft: "funas_term (?clean (Suc ?k)) \<subseteq> F"
            by (rule funas_term_clean_term)+
          have "(?clean ?k,?clean (Suc ?k)) \<in> ?S"
            by (rule sig_stepI[OF strict fs ft])
          moreover have "(?clean ?k,?clean (Suc ?k)) \<notin> ?S"
            using stable[of ?k] by auto
          ultimately show False by contradiction
        qed
        from erased_ostep_updates_one_alien[OF raw cond erased]
        obtain xs a b ys where left: "aliens F (seq ?k) = xs @ a # ys"
          and right: "aliens F (seq (Suc ?k)) = xs @ b # ys"
          and ab: "(a,b) \<in> ?O" by blast
        have ain: "a \<in> set (aliens F (seq ?k))" unfolding left by simp
        have sn_a: "SN_on ?O {a}"
          by (rule alien_SN[OF depth[of ?k] ain])
        have restricted: "(a,b) \<in> restrict_SN ?O ?O"
          unfolding restrict_SN_def using ab sn_a by auto
        show "(?as i,?as (Suc i)) \<in>
            list_singleton_ext (restrict_SN ?O ?O)"
          unfolding list_singleton_ext_def
          using left right restricted by (auto simp: add.assoc)
      qed
      have list_SN: "SN (list_singleton_ext (restrict_SN ?O ?O))"
        by (rule SN_list_singleton_ext, simp)
      have exists_chain: "\<exists>g. g 0 \<in> UNIV \<and>
          chain (list_singleton_ext (restrict_SN ?O ?O)) g"
        by (rule exI[of _ ?as], use alien_chain in simp)
      from list_SN exists_chain show False unfolding SN_defs by contradiction
    qed
  qed
qed

end

end
