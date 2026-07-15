(* Author: René Thiemann *)

text \<open>The aim is to show that whenever a right-linear TRS is looping, 
  then also a loop can be detected by narrowing starting from right-hand sides.\<close>

theory RFC_Loops
  imports
    Right_Forward_Closures.Right_Forward_Closure
    TRS.Sharp_Syntax
begin

definition pos_subst_split :: "('f,'v)term \<Rightarrow> ('f,'v,'w)gsubst \<Rightarrow> pos \<Rightarrow> pos \<times> pos" where
  "pos_subst_split t \<sigma> p = (THE pair. case pair of (p1,p2) \<Rightarrow> p1 @ p2 = p \<and> p1 \<in> var_poss t)" 

lemma pos_subst_split: assumes "p \<in> var_poss (t \<cdot> \<sigma>)" 
  and "pos_subst_split t \<sigma> p = (p1,p2)" 
shows "p1 @ p2 = p" "p1 \<in> var_poss t" "p1' @ p2' = p \<Longrightarrow> p1' \<in> var_poss t \<Longrightarrow> (p1',p2') = (p1,p2)" 
proof (atomize(full), goal_cases)
  case 1
  from assms(1) obtain  p1 p2 where p12: "p1 @ p2 = p" "p1 \<in> var_poss t" 
    by (metis pos_into_subst self_append_conv subst_apply_eq_Var subt_at_subst var_poss_iff)
  have "\<exists>! pair. case pair of (p1,p2) \<Rightarrow> p1 @ p2 = p \<and> p1 \<in> var_poss t" 
  proof (intro ex1I[of _ "(p1,p2)"], use p12 in force, clarify)
    fix p1' p2' 
    assume "p1' \<in> var_poss t" "p = p1' @ p2'" 
    with p12 show "p1' = p1 \<and> p2' = p2"
      by (metis append_eq_append_conv less_eq_pos_simps(1) pos_less_eq_append_not_parallel var_poss_parallel)
  qed
  thus ?case using assms(2)[unfolded pos_subst_split_def]
    by (metis (mono_tags, lifting) old.prod.case the_equality)
qed

context 
  fixes R :: "('f,'v)trs"
begin
definition loopingN :: "nat \<Rightarrow> ('f,'v)term \<Rightarrow> bool" where "loopingN n t = (n \<noteq> 0 \<and> (\<exists> C \<mu>. (t, C \<langle> t \<cdot> \<mu> \<rangle>) \<in> (rstep R)^^n))"
definition looping :: "('f,'v)term \<Rightarrow> bool" where "looping t = (\<exists> C \<mu>. (t, C \<langle> t \<cdot> \<mu> \<rangle>) \<in> (rstep R)\<^sup>+)"
definition minLoopLen :: nat where "minLoopLen = (LEAST n. (\<exists> t. loopingN n t))" 
definition minLoop :: "('f,'v)term \<Rightarrow> bool" where "minLoop t = (loopingN minLoopLen t \<and> (\<forall> t' \<lhd> t. Not (loopingN minLoopLen t')))" 

lemma looping_imp_minLoop: assumes "looping t"
  shows "\<exists> t'. minLoop t'" "m < minLoopLen \<Longrightarrow> \<not> loopingN m s" "minLoopLen \<noteq> 0" 
proof -
  from assms[unfolded looping_def] obtain C \<mu> where "(t, C \<langle> t \<cdot> \<mu> \<rangle>) \<in> (rstep R)\<^sup>+" by auto
  then obtain n where "n \<noteq> 0" and "(t, C \<langle> t \<cdot> \<mu> \<rangle>) \<in> (rstep R)^^n"
    using trancl_power by blast
  hence "\<exists> n. \<exists> t. loopingN n t" unfolding loopingN_def by auto
  from LeastI_ex[OF this, folded minLoopLen_def]
  obtain t where t: "loopingN minLoopLen t" by auto
  from this[unfolded loopingN_def] show "minLoopLen \<noteq> 0" by auto
  {
    fix m s
    assume "m < minLoopLen"   
    from not_less_Least[OF this[unfolded minLoopLen_def]]
    have "\<not> loopingN m s" by auto
  } note minLen = this
  thus "m < minLoopLen \<Longrightarrow> \<not> loopingN m s" .
  from t show "\<exists> t'. minLoop t'" 
  proof (induct t rule: wf_induct[OF wf_measure[of size]])
    case (1 t)
    show ?case
    proof (cases "\<exists> t' \<lhd> t. loopingN minLoopLen t'")
      case True
      then obtain t' where supt: "t' \<lhd> t" and "loopingN minLoopLen t'" by auto
      with 1 supt_size[OF supt] obtain t'' where ml: "minLoop t''" by auto
      thus ?thesis ..
    next
      case False
      with 1(2) show ?thesis by (intro exI[of _ t], auto simp: minLoop_def)
    qed
  qed
qed

private definition rs_step where "rs_step = rrstep R O {\<unrhd>}" 
private definition rs'_step where "rs'_step = {(l \<cdot> \<sigma>, r' \<cdot> \<sigma>) | l r r' \<sigma>. (l,r) \<in> R \<and> is_Fun r' \<and> r \<unrhd> r' \<and> \<not> (l \<rhd> r')}" 
private definition rsn_step where "rsn_step = rs_step \<union> nrrstep R"
private definition rs'n_step where "rs'n_step = rs'_step \<union> nrrstep R"

private lemma rsn_steps'_to_rsteps: assumes "(s,t) \<in> rs'n_step ^^ n" 
  shows "\<exists> C. (s,C\<langle>t\<rangle>) \<in> (rstep R)^^n" 
  using assms
proof (induct n arbitrary: s t)
  case 0
  thus ?case by (auto intro: exI[of _ Hole])
next
  case (Suc n s u)
  from Suc(2) obtain t where "(s,t) \<in> rs'n_step ^^ n" and tu: "(t,u) \<in> rs'n_step" by auto
  from Suc(1)[OF this(1)] obtain C where IH: "(s, C \<langle> t \<rangle>) \<in> (rstep R) ^^ n" ..
  from tu[unfolded rs'n_step_def]
  have "\<exists> D. (t, D\<langle> u \<rangle>) \<in> rstep R" 
  proof
    assume "(t,u) \<in> nrrstep R" 
    hence "(t,u) \<in> rstep R"
      by (simp add: nrrstep_imp_rstep)
    thus ?thesis by (auto intro: exI[of _ Hole])
  next
    assume "(t,u) \<in> rs'_step" 
    from this[unfolded rs'_step_def] obtain l r r' \<sigma> where
      *: "t = l \<cdot> \<sigma>" "u = r' \<cdot> \<sigma>" "r \<unrhd> r'" "(l,r) \<in> R" by auto
    hence "(t, r \<cdot> \<sigma>) \<in> rstep R" "r \<cdot> \<sigma> \<unrhd> u" by auto
    thus ?thesis by force
  qed
  then obtain D where "(t, D \<langle> u \<rangle>) \<in> rstep R" by auto
  hence "(C \<langle>t\<rangle>, C \<langle> D \<langle> u \<rangle> \<rangle>) \<in> rstep R" by auto
  with IH have "(s, C \<langle> D \<langle> u \<rangle> \<rangle>) \<in> (rstep R)^^(Suc n)" by auto
  thus ?case by (intro exI[of _ "C \<circ>\<^sub>c D"], auto)
qed

context
  assumes wf: "wf_trs R" 
begin
private lemma rs_step_swap: "rs_step \<subseteq> rs'_step \<union> {\<rhd>}" 
proof
  fix s u
  assume "(s,u) \<in> rs_step" 
  then obtain t where "(s,t) \<in> rrstep R" and tu: "t \<unrhd> u" unfolding rs_step_def by auto
  then obtain l r \<sigma> where s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" and lr: "(l,r) \<in> R" 
    by (auto elim: rrstepE)
  from tu obtain p where p: "p \<in> poss t" and u: "u = t |_ p"
    using supteq_imp_subt_at by auto
  from poss_subst_choice[OF p[unfolded t]]
  consider (in_r) "p \<in> poss r" "is_Fun (r |_ p)" "\<not> (s \<rhd> u)"  |
     (subt) "s \<rhd> u" |
     (in_sigma) x q1 q2 where "q1 \<in> poss r" "q2 \<in> poss (\<sigma> x)" "r |_ q1 = Var x" "x \<in> vars_term r" "p = q1 @ q2" 
          "r \<cdot> \<sigma> |_ p = \<sigma> x |_ q2" by auto
  thus "(s, u) \<in> rs'_step \<union> {\<rhd>}" 
  proof cases
    case (in_r)
    hence subt: "r \<unrhd> r |_ p" by (intro subt_at_imp_supteq)
    have "\<not> (l \<rhd> r |_p)" 
    proof
      assume "l \<rhd> r |_p" 
      hence "s \<rhd> u" using in_r unfolding s u t by simp
      with in_r show False by auto
    qed
    with subt in_r lr have "(s,u) \<in> rs'_step" unfolding rs'_step_def u s t by auto
    thus ?thesis ..
  next
    case *: (in_sigma)
    from wf[unfolded wf_trs_def] lr *
    have x: "x \<in> vars_term l" by auto
    from wf[unfolded wf_trs_def] lr obtain f ls where l: "l = Fun f ls" by force
    with x have "l \<rhd> Var x" by fastforce
    hence "s \<rhd> \<sigma> x" unfolding s 
      by (metis l subst_image_subterm x)
    moreover from * have "\<sigma> x \<unrhd> u" unfolding u t 
      by (simp add: subt_at_imp_supteq)
    ultimately have "s \<rhd> u"
      using supt_supteq_trans by auto
    thus ?thesis ..
  qed auto
qed
  
private lemma rsn_step_swap: "rsn_step O {\<unrhd>} \<subseteq> {\<unrhd>} O rs'n_step\<^sup>=" 
proof 
  fix s u
  assume "(s,u) \<in> rsn_step O {\<unrhd>}" 
  thus "(s,u) \<in> {\<unrhd>} O rs'n_step\<^sup>=" 
  proof (induct s arbitrary: u rule: wf_induct[OF wf_measure[of size]])
    case (1 s u)
    then obtain t where st: "(s,t) \<in> rsn_step" and tu: "t \<unrhd> u" by auto
    show ?case
    proof (cases "(s,t) \<in> rs_step")
      case True      
      with tu have "(s,u) \<in> rs_step" unfolding rs_step_def 
        by (meson relcomp.simps subterm.dual_order.trans)
      with rs_step_swap
      show ?thesis unfolding rs'n_step_def by blast
    next
      case False
      with st[unfolded rsn_step_def] have st: "(s,t) \<in> nrrstep R" by auto
      show ?thesis 
      proof (cases "t = u")
        case True
        with st show ?thesis unfolding rs'n_step_def by auto
      next
        case False
        with tu have "t \<rhd> u" by blast
        then obtain f ts i where t: "t = Fun f ts" and i: "i < length ts" "ts ! i \<unrhd> u"
          by (metis args_poss subt_at.simps(2) subt_at_imp_supteq supt_imp_subt_at_nepos)
        from st[unfolded t] obtain ss where s: "s = Fun f ss" and len: "length ss = length ts" 
          using nrrstep_args by blast  
        from nrrstep_imp_pos_term[OF st[unfolded s t]] obtain j tj
          where step: "(ss ! j, tj) \<in> rstep R" and j: "j < length ss" and ts: "ts = ss[j := tj]" by auto
        show ?thesis
        proof (cases "i = j")
          case False
          with i j ts t s len have "ts ! i \<in> set ss"
            by (metis in_set_conv_nth nth_list_update_neq)
          with i(2) have "s \<unrhd> u" unfolding s by blast
          thus ?thesis by auto
        next
          case True
          with i j ts t s len have "ts ! i = tj"
            by (meson nth_list_update_eq)
          with i have tj: "tj \<unrhd> u" by auto
          with step have step: "(ss ! j, u) \<in> rsn_step O {\<unrhd>}" unfolding 
            rstep_iff_rrstep_or_nrrstep rsn_step_def rs_step_def by auto
          from s j have arg: "ss ! j \<in> set ss" by auto
          from split_list[OF this] obtain a b where ss: "ss = a @ ss ! j # b" by auto
          from arg_cong[OF this, of "size_list size"] have "size s > size (ss ! j)" 
            unfolding s by auto
          with 1 step have IH: "(ss ! j, u) \<in> {\<unrhd>} O rs'n_step\<^sup>=" by auto
          from arg have "s \<unrhd> ss ! j" unfolding s by auto
          from supteq_trans[OF this] IH
          show ?thesis by blast
        qed
      qed
    qed
  qed
qed
    
private lemma rsteps_supt_to_rs'n_steps: assumes "(r, u) \<in> rstep R ^^ m" "u \<unrhd> s"
  shows "\<exists>m'\<le>m. (r, s) \<in> {\<unrhd>} O rs'n_step ^^ m'"   
  using assms(1-2)
proof (induct m arbitrary: u s)
  case (Suc m u s)
  from Suc(2) obtain v where steps: "(r, v) \<in> (rstep R)^^m" "(v,u) \<in> rstep R" by auto
  with Suc(3) have "(v,s) \<in> rsn_step O {\<unrhd>}" unfolding rsn_step_def rstep_iff_rrstep_or_nrrstep rs_step_def by auto
  with rsn_step_swap obtain w where vw: "v \<unrhd> w" and ws: "(w,s) \<in> rs'n_step\<^sup>=" by auto
  from Suc(1)[OF steps(1) vw] obtain m' where m: "m' \<le> m" and rhsw: "(r, w) \<in> {\<unrhd>} O rs'n_step ^^ m'" 
    by auto
  from rhsw ws have "(r,s) \<in> {\<unrhd>} O rs'n_step ^^ m' \<or> (r,s) \<in> {\<unrhd>} O rs'n_step ^^ Suc m'" by auto
  with m show ?case using le_Suc_eq by blast
qed auto

text \<open>If there is a loop, then there is a loop of minimum length which
  contains at least one root step, and where the final subterm operation \<open>C\<langle>t \<cdot> \<mu>\<rangle> \<unrhd> t \<cdot> \<mu>\<close>
  is integrated into the root steps in a way, that only subterms of right-hand sides are required;
  in particular one does not take a subterm only from the substition part of a root step. This
  is encoded in the restricted version of combining a root step with a subterm: @{const rs'_step}.\<close>
private lemma Ex_loop_imp_rs'_step_seq: assumes "Ex looping"
  shows "\<exists> t \<mu>. (t, t \<cdot> \<mu>) \<in> rs'_step O rs'n_step^^(minLoopLen - 1)" 
proof -
  define n where "n = minLoopLen" 
  from assms(1) obtain t' where "looping t'" by auto
  from looping_imp_minLoop[OF this] obtain t where assms: "minLoop t" by auto
  from this[unfolded loopingN_def minLoop_def] obtain C \<mu> s where st: "s = t \<cdot> \<mu>" and loop: "(t,C \<langle>s\<rangle>) \<in> (rstep R)^^n" 
    and n0: "n \<noteq> 0" 
    by (auto simp: n_def)
  moreover have "(C \<langle> s \<rangle>, s) \<in> {\<unrhd>}" by auto
  ultimately have "(t,s) \<in> (rstep R)^^n O {\<unrhd>}" by auto
  then obtain u where tu: "(t,u) \<in> (rstep R)^^n" and us: "u \<unrhd> s" by auto
  from loop n0 have "(t,C \<langle>s\<rangle>) \<in> (rstep R)\<^sup>+" unfolding trancl_power by auto
  hence "looping t" unfolding st looping_def by auto
  from looping_imp_minLoop[OF this, folded n_def] 
  have nmin: "m < n \<Longrightarrow> \<not> loopingN m v" for m v by auto
  show ?thesis 
  proof (cases "(t,u) \<in> (nrrstep R)^^n")
    case tun: True
    from n0 obtain m where nm: "n = Suc m" by (cases n, auto)
    from tun[unfolded nm]
    obtain v where tv: "(t,v) \<in> nrrstep R" and vum: "(v,u) \<in> (nrrstep R)^^m" 
      by (elim relpow_Suc_E2)
    then obtain f ts where t: "t = Fun f ts" by (cases t, auto simp: nrrstep_def rstep_r_p_s_def)
    from nrrstep_imp_pos_term[OF tv[unfolded t]] obtain i vi where v: "v = Fun f (ts [i := vi])" 
      and tvi: "(ts ! i, vi) \<in> rstep R" and i: "i < length ts" by auto
    from vum have vu: "(v,u) \<in> (nrrstep R)\<^sup>*" unfolding rtrancl_power by auto
    from nrrsteps_preserve_root[OF vu[unfolded v]] obtain us where u: "u = Fun f us" by auto 
    from nrrsteps_imp_eq_root_arg_rsteps[OF vu, unfolded u v] i
    have len: "length us = length ts" and step: "(vi, us ! i) \<in> (rstep R)\<^sup>*" by auto
    from nrrsteps_imp_arg_rsteps_count[OF vum[unfolded v u], of i] obtain k where
      k: "k \<le> m" and vui: "(vi, us ! i) \<in> (rstep R)^^k" using i len by auto
    define l where "l = Suc k" 
    from tvi vui have tu: "(ts ! i, us ! i) \<in> (rstep R)^^l" unfolding l_def by (rule relpow_Suc_I2)
    from k nm have l: "l \<noteq> 0" "l \<le> n" by (auto simp: l_def)
    have "\<exists> i < length ts. \<exists> m \<le> n. loopingN m (ts ! i)" 
    proof (cases "u = s")
      case True
      with tu u st t i have "(ts ! i, ts ! i \<cdot> \<mu>) \<in> (rstep R)^^l" by auto
      hence "loopingN l (ts ! i)" unfolding loopingN_def using l(1) 
        by (intro exI[of _ Hole] exI[of _ \<mu>] conjI, auto)
      with i l show ?thesis by auto
    next
      case False
      from us False have "u \<rhd> s" by auto
      from this[unfolded u] len obtain i where i: "i < length ts" and us: "us ! i \<unrhd> s"
        by (metis in_set_conv_nth supt_Fun_imp_arg_supteq)  
      from nrrsteps_imp_arg_rsteps_count[OF tun[unfolded t u]] i len obtain m where
        ts_us: "(ts ! i, us ! i) \<in> (rstep R)^^m" and mn: "m \<le> n" by auto
      from us[unfolded st t] i len have us_ts: "us ! i \<unrhd> ts ! i \<cdot> \<mu>"
        by (metis nth_mem subterm.order.trans supteq.refl supteq.subt supteq_subst)
      from ts_us have "m \<noteq> 0 \<or> us ! i = ts ! i" by (cases m, auto)
      thus ?thesis
      proof
        assume "m \<noteq> 0" 
        with ts_us us_ts have "loopingN m (ts ! i)" unfolding loopingN_def by fastforce
        with i mn show ?thesis by auto
      next
        assume "us ! i = ts ! i" 
        from us[unfolded this st t] i have False
          by (meson leD nth_mem set_supteq_into_supt size_subst supt_size)
        thus ?thesis ..
      qed
    qed
    then obtain i m where i: "i < length ts" and m: "m \<le> n" and loop: "loopingN m (ts ! i)" by auto
    from nmin[of m] loop have "m \<ge> n" by fastforce
    with m have m: "m = n" by auto
    with loop have loop: "loopingN minLoopLen (ts ! i)" unfolding n_def by auto
    with assms have False unfolding minLoop_def t using i by auto
    thus ?thesis ..
  next
    case tu_nrr: False
    from tu[unfolded relpow_fun_conv]
    obtain f where f: "f 0 = t" "f n = u" and steps: "\<And> i. i < n \<Longrightarrow> (f i, f (Suc i)) \<in> rstep R" by auto
    define P where "P i = (i < n \<and> (f i, f (Suc i)) \<in> rrstep R)" for i
    have exP: "Ex P" 
    proof (rule ccontr)
      assume contr: "\<not> ?thesis" 
      have "(t,u) \<in> (nrrstep R)^^n" unfolding relpow_fun_conv
      proof (intro exI[of _ f] conjI f allI impI)
        fix i
        assume "i < n" 
        with steps[OF this] contr
        show "(f i, f (Suc i)) \<in> nrrstep R" unfolding rstep_iff_rrstep_or_nrrstep P_def by auto
      qed
      with tu_nrr show False ..
    qed
    then obtain ri where ri: "ri < n" and step: "(f ri, f (Suc ri)) \<in> rrstep R" unfolding P_def by auto
    define lhs where "lhs = f ri" 
    define rhs where "rhs = f (Suc ri)" 
    from step have two: "(lhs, rhs) \<in> rrstep R" unfolding lhs_def rhs_def by auto
    define m where "m = n - ri - Suc 0" 
    have n_split: "n = ri + Suc 0 + m" unfolding m_def using ri by linarith
    have one: "(t, lhs) \<in> (rstep R)^^ri" 
      unfolding relpow_fun_conv lhs_def
      by (intro exI[of _ f], insert f ri steps, auto)
    have three: "(rhs, u) \<in> (rstep R)^^m" 
      unfolding relpow_fun_conv rhs_def
    proof (intro exI[of _ "\<lambda> i. f (i + Suc ri)"] conjI allI impI)
      show "f (m + Suc ri) = u" unfolding f(2)[symmetric] unfolding n_split 
        by (auto simp: ac_simps)
    qed (insert steps, auto simp: n_split)
    from us obtain C where u: "u = C \<langle> t \<cdot> \<mu>\<rangle>" unfolding st by auto
    from subst.closedD[OF subst.closed_relpow[OF subst_closed_rstep] one]
    have "(t \<cdot> \<mu>, lhs \<cdot> \<mu>) \<in> rstep R ^^ ri" .
    from ctxt.closedD[OF ctxt.closed_relpow[OF ctxt_closed_rstep] this]
    have one: "(C\<langle>t \<cdot> \<mu>\<rangle>, C\<langle>lhs \<cdot> \<mu>\<rangle>) \<in> rstep R ^^ ri" .
    from three one[folded u] 
    have "(rhs, C\<langle>lhs \<cdot> \<mu>\<rangle>) \<in> rstep R ^^ (m + ri)" by (rule relpow_trans)
    also have "m + ri = n - 1" unfolding n_split by simp
    finally have "(rhs, C\<langle>lhs \<cdot> \<mu>\<rangle>) \<in> rstep R ^^ (n - 1)" .
    from rsteps_supt_to_rs'n_steps[OF this ctxt_imp_supteq]
    obtain m v where "m \<le> n - 1" and sub: "rhs \<unrhd> v" and vs: "(v, lhs \<cdot> \<mu>) \<in> rs'n_step ^^ m" by auto
    with n0 have m: "m < n" by auto
    from two sub have "(lhs,v) \<in> rs_step" unfolding rs_step_def by auto
    with rs_step_swap 
    have "(lhs,v) \<in> rs'_step \<or> lhs \<rhd> v" by auto
    hence lhsv: "(lhs,v) \<in> rs'_step" 
    proof
      assume lhsv: "lhs \<rhd> v"
      then obtain D where D: "D \<noteq> Hole" and lhs: "lhs = D \<langle> v \<rangle>" by auto
      from rsn_steps'_to_rsteps[OF vs, unfolded st]
      obtain C where three: "(v, C\<langle>lhs \<cdot> \<mu>\<rangle>) \<in> rstep R ^^ m" by auto
      define E where  "E = C \<circ>\<^sub>c (D \<cdot>\<^sub>c \<mu>)" 
      from lhs have lhs: "C \<langle> lhs \<cdot> \<mu> \<rangle> = E \<langle> v \<cdot> \<mu> \<rangle>" by (auto simp: E_def)
      from D have E: "E \<noteq> Hole" unfolding E_def by (cases C; cases D; auto)
      from three[unfolded lhs] have loop: "(v, E\<langle>v \<cdot> \<mu>\<rangle>) \<in> rstep R ^^ m" .
      from nmin[OF m, of v] loop have m0: "m = 0" unfolding loopingN_def by auto
      with loop have "v = E \<langle> v \<cdot> \<mu> \<rangle>"
        by (meson relpow_0_E) 
      with E have False by auto
      thus ?thesis ..
    qed
    from lhsv have "(lhs,v) \<in> rs'n_step" unfolding rs'n_step_def by auto
    from this vs have "(lhs, lhs \<cdot> \<mu>) \<in> rs'n_step ^^ (Suc m)" by (rule relpow_Suc_I2)
    from rsn_steps'_to_rsteps[OF this] have "loopingN (Suc m) lhs" unfolding loopingN_def by blast
    with nmin[of "Suc m" lhs] have "Suc m \<ge> n" by linarith
    with m have m: "m = n - 1" by linarith
    from lhsv vs show ?thesis unfolding m unfolding n_def by auto
  qed
qed

text \<open>A result of our FroCoS 2005 paper: if a TRS is looping, then there also is a DP loop.
  This result is true for any sharp-function, e.g., both identity and chosing fresh sharp-symbols.\<close>
theorem Ex_looping_to_DP_loop: assumes "Ex looping" 
    and P: "P = DP shp R" 
  shows "\<exists>t \<mu>. (t, t \<cdot> \<mu>) \<in> rrstep P O (rrstep P \<union> nrrstep R) ^^ (minLoopLen - 1)" 
proof -
  define n where "n = minLoopLen - 1" 
  define D where "D = {f. defined R f}"  
  from Ex_loop_imp_rs'_step_seq[OF assms(1), folded n_def]
  obtain t \<mu> where "(t, t \<cdot> \<mu>) \<in> rs'_step O rs'n_step ^^ n" by auto
  then obtain s where step: "(t,s) \<in> rs'_step" and steps: "(s, t \<cdot> \<mu>) \<in> rs'n_step ^^ n" by auto
  {
    from this[unfolded rs'_step_def] obtain l r \<sigma> where lr: "(l,r) \<in> R" and t: "t = l \<cdot> \<sigma>" by auto
    with wf[unfolded wf_trs_def] obtain f ls where l: "l = Fun f ls" by (cases l, auto)
    from l lr have "(f,length ls) \<in> D" unfolding D_def defined_def by auto
    with t l have "root t \<in> Some ` D" "root (t \<cdot> \<mu>) \<in> Some ` D" by auto
  } note roots = this
  let ?shp = "sharp_term shp" 
  {
    fix s t :: "('f,'v)term" 
    assume "(s,t) \<in> rs'_step" and rt: "root t \<in> Some ` D" 
    from this(1)[unfolded rs'_step_def] obtain l r r' \<sigma> where 
      *: "s = l \<cdot> \<sigma>" "t = r' \<cdot> \<sigma>" "r \<unrhd> r'" "is_Fun r'" "(l,r) \<in> R" "(l, r') \<notin> {\<rhd>}" 
      by auto
    from * wf[unfolded wf_trs_def] obtain f ls where l: "l = Fun f ls" by (cases l, auto)
    from l * have rts: "root s \<in> Some ` D" unfolding * D_def by (force simp: defined_def)
    from * obtain g ts where r': "r' = Fun g ts" by (cases r', auto)
    let ?g = "(g,length ts)" 
    from rt r' * have "root r' \<in> Some ` D" by auto
    with l * r' have inP: "(?shp l, ?shp r') \<in> P" unfolding assms DP_on_def D_def[symmetric] 
      apply (intro CollectI, unfold split)
      apply (rule exI[of _ l], rule exI[of _ r], rule exI[of _ g], rule exI[of _ ts])
      by auto
    hence "(?shp s, ?shp t) \<in> rrstep P" unfolding * l r' by auto
    note this rts
  } note rs'_step = this
  {
    fix s t :: "('f,'v)term" 
    assume st: "(s,t) \<in> nrrstep R" and rt: "root t \<in> Some ` D" 
    hence rts: "root s \<in> Some ` D"
      by (metis nrrsteps_imp_eq_root_arg_rsteps r_into_rtrancl)
    from st have "(?shp s, ?shp t) \<in> nrrstep R" by (rule nrrstep_imp_sharp_nrrstep)
    note this rts
  } note nrr_step = this
  {
    fix s t :: "('f,'v)term" 
    assume st: "(s,t) \<in> rs'n_step" and rt: "root t \<in> Some ` D" 
    from nrr_step[OF _ rt, of s] rs'_step[OF _ rt, of s] st
    have "(?shp s, ?shp t) \<in> rrstep P \<union> nrrstep R" "root s \<in> Some ` D" 
      unfolding rs'n_step_def by auto
  } note rs'n_step = this
  define tmu where "tmu = t \<cdot> \<mu>" 
  from steps roots(2)
  have "(?shp s, ?shp (t \<cdot> \<mu>)) \<in> (rrstep P \<union> nrrstep R)^^n \<and> root s \<in> Some ` D" 
    unfolding tmu_def[symmetric] 
  proof (induct n arbitrary: tmu)
    case (Suc n u)
    from Suc(2) obtain t where steps: "(s, t) \<in> rs'n_step ^^ n" and step: "(t,u) \<in> rs'n_step" by auto
    from rs'n_step[OF step Suc(3)] 
    have step: "(?shp t, ?shp u) \<in> rrstep P \<union> nrrstep R" and 
      rt: "root t \<in> Some ` D" 
      by auto
    from Suc(1)[OF steps rt] step 
    show ?case by auto
  qed auto
  hence steps: "(?shp s, ?shp (t \<cdot> \<mu>)) \<in> (rrstep P \<union> nrrstep R)^^n" 
    and rts: "root s \<in> Some ` D" by auto
  from rs'_step[OF step rts] 
  have step: "(?shp t, ?shp s) \<in> rrstep P" by auto
  from roots(1) have "?shp (t \<cdot> \<mu>) = ?shp t \<cdot> \<mu>" by (cases t, auto)
  from step steps[unfolded this]
  have "(?shp t, ?shp t \<cdot> \<mu>) \<in> rrstep P O (rrstep P \<union> nrrstep R)^^n" by auto
  thus ?thesis unfolding n_def by auto
qed
end
end

context 
  fixes R P :: "('f,'v :: infinite)trs" and ren :: "'v renaming2" 
  assumes wf: "wf_trs R" "wf_trs P" 
begin

lemma DP_loop_to_narrow_seq_RL: assumes "(s, s \<cdot> \<delta>) \<in> rrstep P O (rrstep P \<union> nrrstep R) ^^ n" 
  and rlR: "\<And> lr. lr \<in> R \<Longrightarrow> linear_term (snd lr)" 
  and rlP: "\<And> lr. lr \<in> P \<Longrightarrow> linear_term (snd lr)" 
  and rhsP: "\<And> lr. lr \<in> P \<Longrightarrow> is_Fun (snd lr)" 
  shows foo
proof -
  let ?P = "rrstep P" 
  let ?R = "nrrstep R"
  let ?Rp = "rstep_pos R" 
  let ?PR = "?P \<union> ?R"  
  from assms(1) obtain t where st: "(s,t) \<in> ?P" and steps: "(t,s \<cdot> \<delta>) \<in> ?PR^^n" by auto
  from rrstepE[OF this(1)] obtain l0 r0 \<sigma>0 where lr0: "(l0,r0) \<in> P" and s: "s = l0 \<cdot> \<sigma>0" and t: "t = r0 \<cdot> \<sigma>0" by auto
  from st have st: "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> ?P"
    by (meson subst.closedD subst_closed_rrstep)
  from rlP[OF lr0] have rlin: "linear_term r0" by auto
  from rhsP[OF lr0] have rFun: "is_Fun r0" by auto
  from steps[unfolded relpow_fun_conv] obtain v where v0n: "v 0 = t" "v n = s \<cdot> \<delta>" 
     and steps: "\<And> i. i < n \<Longrightarrow> (v i, v (Suc i)) \<in> ?PR" by blast
  define m where "m = Suc n"
  define u where "u = v(m := t \<cdot> \<delta>)" 
  have u0r0: "u 0 = r0 \<cdot> \<sigma>0" unfolding u_def m_def using v0n t by auto
  {
    fix i
    assume "i < m" 
    hence "i < n \<or> i = n" unfolding m_def by auto
    hence "(u i, u (Suc i)) \<in> ?PR" 
      using steps[of i] v0n st unfolding u_def m_def by auto
  } note steps = this
  have u0m: "u 0 = t" "u m = t \<cdot> \<delta>" 
    using v0n unfolding m_def u_def by auto
  define Pn where "Pn i = (if i = n then {(l0,r0)} else P)" for i
  let ?Pn = "\<lambda> i. rrstep (Pn i)" 
  have stepn: "(u n, u (Suc n)) \<in> ?Pn n" unfolding u_def using v0n lr0 m_def 
    unfolding Pn_def apply (simp add: s t)
    apply (intro rrstepI[of l0 r0 _ _ "\<sigma>0 \<circ>\<^sub>s \<delta>"])
    by auto
  let ?step = "\<lambda> b i. (b \<longrightarrow> (u i, u (Suc i)) \<in> ?Pn i) \<and> (\<not> b \<longrightarrow> (u i, u (Suc i)) \<in> ?R)"
  {
    fix i
    assume "i < m" 
    from steps[OF this] 
    have "(u i, u (Suc i)) \<in> ?P \<or> (u i, u (Suc i)) \<in> ?R" by auto
    hence "(u i, u (Suc i)) \<in> ?Pn i \<or> (u i, u (Suc i)) \<in> ?R" using stepn 
      unfolding Pn_def by (cases "i = n", auto) 
    hence "\<exists> b. ?step b i \<and> (i = n \<longrightarrow> b)" using stepn by (cases "i = n", auto)
  }
  hence "\<forall> i. \<exists> b. i < m \<longrightarrow> (?step b i \<and> (i = n \<longrightarrow> b))" by metis
  from choice[OF this] obtain b where "\<And> i. i < m \<Longrightarrow> ?step (b i) i" and 
    bn: "b n" by (auto simp: m_def)
  hence Psteps: "\<And> i. i < m \<Longrightarrow> b i \<Longrightarrow> (u i, u (Suc i)) \<in> ?Pn i" 
    and Rsteps: "\<And> i. i < m \<Longrightarrow> \<not> b i \<Longrightarrow> (u i, u (Suc i)) \<in> ?R" by auto
  define cond where "cond i lr \<sigma> p = (if b i then (u i, u (Suc i)) \<in> rstep_r_p_s (Pn i) lr [] \<sigma> \<and> p = []
      else ((u i, u (Suc i)) \<in> rstep_r_p_s R lr p \<sigma> \<and> p \<noteq> []))" for i lr \<sigma> p 
  {
    fix i
    assume "i < m" and bi: "b i" 
    from Psteps[OF this] obtain lr \<sigma> where "(u i, u (Suc i)) \<in> rstep_r_p_s (Pn i) lr [] \<sigma>"
      using rrstep_def by fastforce
    hence "cond i lr \<sigma> []" using bi unfolding cond_def by auto
    hence "\<exists> lr \<sigma> p. cond i lr \<sigma> p" by blast
  } note Pcase = this
  {
    fix i
    assume "i < m" and bi: "\<not> b i" 
    from Rsteps[OF this] obtain p lr \<tau> where "(u i, u (Suc i)) \<in> rstep_r_p_s R lr p \<tau>"
      and "p \<noteq> []"
      by (smt (verit) mem_Collect_eq neq_Nil_conv nrrstep_def old.prod.case)
    hence "cond i lr \<tau> p" using bi unfolding cond_def by auto
    hence "\<exists> lr \<tau> p. cond i lr \<tau> p" by blast
  } note Rcase = this
  from Pcase Rcase have "\<forall> i. \<exists> lr \<tau> p. i < m \<longrightarrow> cond i lr \<tau> p" by blast
  from choice[OF this] obtain lr where "\<forall> i. \<exists> \<tau> p. i < m \<longrightarrow> cond i (lr i) \<tau> p" by blast
  from choice[OF this] obtain \<tau> where "\<forall> i. \<exists> p. i < m \<longrightarrow> cond i (lr i) (\<tau> i) p" by blast
  from choice[OF this] obtain p where cond: "\<And> i. i < m \<Longrightarrow> cond i (lr i) (\<tau> i) (p i)" by blast
  define S where "S i = (if b i then Pn i else R)" for i
  define Rel where "Rel i = rstep_r_p_s (S i) (lr i) (p i) (\<tau> i)" for i
  have Rel: "(u i, u (Suc i)) \<in> Rel i" if "i < m" for i  using cond[OF that]
    unfolding cond_def Rel_def S_def by (cases "b i", auto)

  define Rel2 where "Rel2 k i = rstep_r_p_s (S i) (lr i) (p i) (\<tau> i \<circ>\<^sub>s \<delta>^^k)" for i k
  define v where "v k i = u i \<cdot> \<delta>^^k" for i k
  have Rel2: "(v k i, v k (Suc i)) \<in> Rel2 k i" if "i < m" for i k using Rel[OF that]
    unfolding v_def Rel_def Rel2_def by (rule rstep_r_p_s_subst)
  have vm0: "v k m = v (Suc k) 0" for k unfolding v_def u0m by auto
  have jm: "j mod m < m" for j unfolding m_def by auto

  (* now let us iterate the sequence *)
  define w where "w j = v (j div m) (j mod m)" for j
  have vSuc: "v (j div m) (Suc (j mod m)) = v (Suc j div m) (Suc j mod m)" for j
    using vm0[of "j div m"] by (simp add: div_Suc mod_Suc)
   
  have wRel2: "(w j, w (Suc j)) \<in> Rel2 (j div m) (j mod m)" for j
    using Rel2[OF jm, of "j div m" j] unfolding w_def vSuc .
  define narr where "narr j = narrows_r_p_s ren (S (j mod m)) (lr (j mod m)) (p (j mod m))" for j

  let ?cond = "\<lambda> j t (\<sigma> :: ('f,'v)subst). linear_term t \<and> is_Fun t \<and> t \<cdot> \<sigma> = w j" 
  let ?cond2 = "\<lambda> j (t :: ('f,'v)term) (\<sigma> :: ('f,'v)subst) (t' :: ('f,'v)term) (\<sigma>' :: ('f,'v)subst). 
      p (j mod m) \<in> fun_poss t \<and> (\<exists> \<mu>. (t, t') \<in> narr j \<mu> \<and> \<sigma> = \<mu> \<circ>\<^sub>s \<sigma>' \<and> (subst_term_mset t' \<sigma>', subst_term_mset t \<sigma>) \<in> (mult {\<lhd>})\<^sup>=) \<or>
      (\<not> b (j mod m) \<and> t' = t \<and>  p (j mod m) \<notin> fun_poss t \<and> (subst_term_mset t \<sigma>', subst_term_mset t \<sigma>) \<in> mult1 ((rstep R)\<inverse>))"

  have cond0: "?cond 0 r0 \<sigma>0" unfolding w_def v_def 
    using u0r0 rFun rlin by auto 
  {
    fix i
    assume "i < m" 
    from cond[OF this, unfolded cond_def] have "lr i \<in> Pn i \<union> R" 
      unfolding rstep_r_p_s_def' by (cases "b i"; force)
    hence "lr i \<in> P \<union> R" using lr0 unfolding Pn_def by (auto split: if_splits)
    with wf rlR[of "lr i"] rlP[of "lr i"] have "\<exists> l r. lr i = (l,r) \<and> linear_term r \<and> vars_term r \<subseteq> vars_term l"
      unfolding wf_trs_def by (cases "lr i", force) 
  } note lr = this

  {
    fix j and t \<sigma>
    assume "?cond j t \<sigma>" 
    hence lin: "linear_term t" and t: "is_Fun t" and match: "t \<cdot> \<sigma> = w j" by auto
    define i where "i = j mod m" 
    define k where "k = j div m" 
    from wRel2[of j, folded k_def i_def]
    have rel: "(w j, w (Suc j)) \<in> Rel2 k i" .
    from lr0 have PnP: "Pn i \<subseteq> P" for i unfolding Pn_def by auto
    {
      assume b: "b i" 
      from cond[of i] b have pi: "p i = []" unfolding i_def cond_def using jm[of j] by auto
      with rel[unfolded Rel2_def] b match
      have step: "(t \<cdot> \<sigma>, w (Suc j)) \<in> rstep_r_p_s (Pn i) (lr i) [] (\<tau> i \<circ>\<^sub>s \<delta> ^^ k)" 
        by (auto simp: S_def)
      from step[unfolded rstep_r_p_s_def'] have lri: "lr i \<in> Pn i" by auto
      hence isFun: "is_Fun (snd (lr i))" using rhsP[of "lr i"] PnP by auto
      have "i < m" unfolding i_def m_def by auto
      from lr[OF this] obtain l r where lri: "lr i = (l,r)" and 
        linr: "linear_term r" and vars: "vars_term r \<subseteq> vars_term l" by auto
      from t have fp: "[] \<in> fun_poss t" by auto
      from narrowing_right_linear_one_step_simulation_r_p_s[OF step[unfolded lri] lin linr vars, of ren, folded lri] this
      obtain \<mu> \<mu>2 \<sigma>' t' where narr: "(t, t') \<in> narrows_r_p_s ren (Pn i) (lr i) [] \<mu>"
        and match: "w (Suc j) = t' \<cdot> \<sigma>'" and sig: "\<sigma> = \<mu> \<circ>\<^sub>s \<sigma>'" and tau: "\<tau> i \<circ>\<^sub>s \<delta> ^^ k = \<mu>2 \<circ>\<^sub>s \<sigma>'" 
        and decr: "(subst_term_mset t' \<sigma>', subst_term_mset t \<sigma>) \<in> (mult {\<lhd>})\<^sup>=" 
        by blast
      from narr isFun have isFun: "is_Fun t'" unfolding narrows_r_p_s_def by auto
      from right_linear_rule_narrowing[OF linr lin narr[unfolded lri]]
      have lint': "linear_term t'" by auto
      from narr pi b have narr: "(t,t') \<in> narr j \<mu>" unfolding narr_def i_def S_def by auto
      have cond: "?cond (Suc j) t' \<sigma>'" using match lint' isFun by auto
      have cond2: "?cond2 j t \<sigma> t' \<sigma>'" using b narr sig tau fp[folded pi] decr unfolding i_def k_def by auto
      from cond cond2 have "\<exists> t' \<sigma>'. ?cond (Suc j) t' \<sigma>' \<and> ?cond2 j t \<sigma> t' \<sigma>'" by blast
    } 
    moreover
    {
      assume b: "\<not> b i" 
      from cond[of i] b have pi: "p i \<noteq> []" unfolding i_def cond_def using jm[of j] by auto
      with rel[unfolded Rel2_def] b match
      have step: "(t \<cdot> \<sigma>, w (Suc j)) \<in> rstep_r_p_s R (lr i) (p i) (\<tau> i \<circ>\<^sub>s \<delta> ^^ k)" 
        by (auto simp: S_def)
      then obtain l r where lri: "lr i = (l,r)" and lr: "(l,r) \<in> R" unfolding rstep_r_p_s_def' by (cases "lr i", auto)
      from rlR[OF lr] have linr: "linear_term r" by auto
      from wf(1)[unfolded wf_trs_def] lr have "vars_term r \<subseteq> vars_term l" by force
      from narrowing_right_linear_one_step_simulation_r_p_s[OF step[unfolded lri] lin linr this, of ren, folded lri]
      consider (inSig) \<sigma>' where "w (Suc j) = t \<cdot> \<sigma>'" "(subst_term_mset t \<sigma>', subst_term_mset t \<sigma>) \<in> mult1 ((rstep R)\<inverse>)"
            "p i \<notin> fun_poss t" 
        | (nstep) \<mu>1 \<mu>2 \<sigma>' t' where
             "w (Suc j) = t' \<cdot> \<sigma>'" "linear_term t'" "(t, t') \<in> narrows_r_p_s ren R (lr i) (p i) \<mu>1" 
             "\<sigma> = \<mu>1 \<circ>\<^sub>s \<sigma>'" "\<tau> i \<circ>\<^sub>s \<delta> ^^ k = \<mu>2 \<circ>\<^sub>s \<sigma>'" "(subst_term_mset t' \<sigma>', subst_term_mset t \<sigma>) \<in> (mult {\<lhd>})\<^sup>=" 
             "p i \<in> fun_poss t" 
        by metis
      hence "\<exists> t' \<sigma>'. ?cond (Suc j) t' \<sigma>' \<and> ?cond2 j t \<sigma> t' \<sigma>'"
      proof cases
        case (inSig \<sigma>')
        then show ?thesis using t lin b match 
          by (intro exI[of _ t] exI[of _ \<sigma>'], auto simp: i_def k_def)
      next
        case *: (nstep \<mu>1 \<mu>2 \<sigma>' t')
        from *(3) pi t have t': "is_Fun t'" unfolding narrows_r_p_s_def
          by (cases t, auto)
        with lin * have cond: "?cond (Suc j) t' \<sigma>'" by auto
        from *(3) b have "(t,t') \<in> narr j \<mu>1" unfolding narr_def S_def i_def by auto
        with * b have cond2: "?cond2 j t \<sigma> t' \<sigma>'" unfolding i_def k_def by auto
        from cond cond2 show ?thesis by blast
      qed
    }
    ultimately have "\<exists> t' \<sigma>'. ?cond (Suc j) t' \<sigma>' \<and> ?cond2 j t \<sigma> t' \<sigma>'" by blast
  }
  from dependent_nat_choice2_start[of ?cond _ _ ?cond2, OF cond0 this] 
  have "\<exists>t \<sigma>. t 0 = r0 \<and> \<sigma> 0 = \<sigma>0 \<and> (\<forall>j. ?cond j (t j) (\<sigma> j) \<and> ?cond2 j (t j) (\<sigma> j) (t (Suc j)) (\<sigma> (Suc j)))" .
  then obtain t \<sigma> where 0: "t 0 = r0" "\<sigma> 0 = \<sigma>0" 
    "\<And> j. ?cond j (t j) (\<sigma> j)" 
    and cond2: "\<And> j. ?cond2 j (t j) (\<sigma> j) (t (Suc j)) (\<sigma> (Suc j))" 
    by blast
  hence match: "t j \<cdot> \<sigma> j = w j" and lint: "linear_term (t j)" for j by auto
  define TS where "TS j = subst_term_mset (t j) (\<sigma> j)" for j
  define t' where "t' i k = t (i + k * m)" for i k
  define \<sigma>' where "\<sigma>' i k = \<sigma> (i + k * m)" for i k
  let ?cond2' = "\<lambda> j \<mu>1. (t j, t (Suc j)) \<in> narr j \<mu>1 \<and> 
         \<sigma> j = \<mu>1 \<circ>\<^sub>s \<sigma> (Suc j) \<and> (TS (Suc j), TS j) \<in> (mult {\<lhd>})\<^sup>= \<and>
         p (j mod m) \<in> fun_poss (t j)
      \<or> \<not> b (j mod m) \<and> t (Suc j) = t j \<and> (TS (Suc j), TS j) \<in> mult1 ((rstep R)\<inverse>) \<and> p (j mod m) \<notin> fun_poss (t j)" 
  from cond2 have "\<forall> j. \<exists>\<mu>1. ?cond2' j \<mu>1" unfolding TS_def by metis
  from choice[OF this] obtain \<mu>1 where cond2': "\<And> j. ?cond2' j (\<mu>1 j)" by auto
  define \<mu>1' where "\<mu>1' i k = \<mu>1 (i + k * m)" for i k
  define N where "N = (\<Union> j. narr j (\<mu>1 j))" 
  {
    fix j l
    have "(t j, t (j + l)) \<in> N\<^sup>*" 
    proof (induct l)
      case (Suc l)
      from cond2'[of "j + l"] have "(t (j + l), t (j + Suc l)) \<in> N\<^sup>=" unfolding N_def by auto
      with Suc show ?case by auto
    qed auto
  } 
  hence narrow_steps: "j \<le> j' \<Longrightarrow> (t j, t j') \<in> N\<^sup>*" for j j'
    by (metis le_iff_add)
  {
    fix i k
    define j where "j = i + k * m"  
    assume i: "i < m" 
    hence i: "i = j mod m" and k: "k = j div m" 
      unfolding j_def by auto
    have "t' i k \<cdot> \<sigma>' i k = t j \<cdot> \<sigma> j" unfolding j_def t'_def \<sigma>'_def by auto
    also have "\<dots> = w j" by (rule match)
    also have "\<dots> = v k i" unfolding w_def i k ..
    also have "\<dots> = u i \<cdot> \<delta> ^^ k" unfolding v_def ..
    finally have "t' i k \<cdot> \<sigma>' i k = u i \<cdot> \<delta> ^^ k" .
  } note match2 = this
  have nmm[simp]: "n mod m = n" unfolding m_def by auto
  from bn have pn: "p n = []" by (metis cond cond_def jm nmm)
  have lrn: "lr n = (l0,r0)" using cond[of n] bn unfolding cond_def Pn_def 
    unfolding m_def rstep_r_p_s_def' by auto
  (* let us show that the t i k terms are increasing in k *)
  {
    fix i k pair
    have "pair = (i,k) \<Longrightarrow> i \<le> m \<Longrightarrow>  \<exists> \<gamma>. t' i k \<cdot> \<gamma> = (t' i (Suc k))"
    proof (induct pair arbitrary: i k rule: wf_induct[OF wf_measures[of "[snd,fst]"]])
      case (1 pair i k)
      note IH = 1(1)[unfolded 1(2), rule_format, OF _ refl]
      have i: "i \<le> m" by fact
      have pair: "pair = (i,k)" by fact 
      show ?case
      proof (cases "pair = (0,0)")
        case True
        hence "i = 0" "k = 0" using pair by auto
        hence "t' i k = t 0" "t' i (Suc k) = t m" unfolding t'_def by auto
        with 0 have id: "t' i k = r0" "t' i (Suc k) = t m" by auto
        from cond2'[of n] have "(t n, t m) \<in> narr n (\<mu>1 n)" unfolding m_def using bn by auto
        from this[unfolded narr_def nmm pn lrn]
        have "(t n, t m) \<in> narrows_r_p_s ren (S n) (l0, r0) [] (\<mu>1 n)" by auto
        from this[unfolded narrows_r_p_s_def] obtain \<mu>2 where
          tm: "t m = r0 \<cdot> \<mu>2" by auto
        show ?thesis unfolding id tm by auto
      next
        case 00: False
        show ?thesis
        proof (cases "i = 0")
          case True
          with 00 pair obtain k' where k: "k = Suc k'" by (cases k, auto)
          from IH[of m k'] obtain \<gamma> where
            IH: "t' m k' \<cdot> \<gamma> = t' m (Suc k')" unfolding k by auto
          thus ?thesis unfolding True k t'_def by auto
        next
          case False
          then obtain i' where ii: "i = Suc i'" by (cases i, auto)
          with i have i': "i' < m" by auto
          from IH[of i' k] i' ii 
          obtain \<gamma> where IH: "t' i' k \<cdot> \<gamma> = t' i' (Suc k)" by auto
          define j where "j = i' + k * m"
          have jm: "j mod m = i'" unfolding j_def using i' by auto
          have id1: "t' i' k = t j" "t' i k = t (Suc j)" 
            unfolding t'_def j_def ii by (auto simp: field_simps)
          have id2: "t' i' (Suc k) = t (j + m)" "t' i (Suc k) = t (Suc (j + m))"
            unfolding ii t'_def j_def by (auto simp: field_simps)
          from IH id1 id2 
          have IH: "t j \<cdot> \<gamma> = t (j + m)" by auto          
          have sub: "fun_poss (t j) \<subseteq> fun_poss (t (j + m))" unfolding IH[symmetric] 
            by (rule fun_poss_subst_sub)
          from cond2'[of j] 
          have first: "(t j, t (Suc j)) \<in> narr j (\<mu>1 j) \<and> p i' \<in> fun_poss (t j) 
            \<or> \<not> b i' \<and> t (Suc j) = t j \<and> p i' \<notin> fun_poss (t j)" 
            by (auto simp: jm)
          from cond2'[of "j + m"]
          have later: "(t (j + m), t (Suc (j + m))) \<in> narr (j + m) (\<mu>1 (j + m)) \<and> p i' \<in> fun_poss (t (j + m)) \<or> 
            \<not> b i' \<and> t (Suc (j + m)) = t (j + m) \<and> p i' \<notin> fun_poss (t (j + m))" by (auto simp: jm)
          have "\<exists> \<gamma>. t (Suc j) \<cdot> \<gamma> = t (Suc (j + m))" 
          proof (cases "p i' \<in> fun_poss (t (j + m))")
            case False (* two identity steps *)
            with later have id: "t (Suc (j + m)) = t (j + m)" by auto
            from False sub first have id': "t (Suc j) = t j" by auto
            show ?thesis using IH unfolding id id' by auto
          next
            case pi_late: True
            with later have later: "(t (j + m), t (Suc (j + m))) \<in> narr (j + m) (\<mu>1 (j + m))" by auto
            from lr[OF i'] obtain l r where lri: "lr i' = (l,r)" "vars_term r \<subseteq> vars_term l" "linear_term r" by auto              
            show ?thesis
            proof (cases "p i' \<in> fun_poss (t j)")
              case True (* two narrow steps at same position *)
              with first have "(t j, t (Suc j)) \<in> narr j (\<mu>1 j)" by auto
              from this[unfolded narr_def jm lri]
              have first: "(t j, t (Suc j)) \<in> narrows_r_p_s ren (S i') (l, r) (p i') (\<mu>1 j)" .
              have "(j + m) mod m = i'" using jm by simp
              from later[unfolded narr_def this] IH lri
              have later: "(t j \<cdot> \<gamma>, t (Suc (j + m))) \<in> narrows_r_p_s ren (S i') (l, r) (p i') (\<mu>1 (j + m))" by auto
              from narrow_instance_pos_in_term[OF first later]
              show ?thesis by auto
            next
              case nmem: False (* one narrow step, one identity step *)
              with first have first: "t (Suc j) = t j" by auto
              from later nmem pi_late 
              have *: "(t j \<cdot> \<gamma>, t (Suc (j + m))) \<in> narrows_r_p_s ren (S ((j + m) mod m)) (lr i') (p i') (\<mu>1 (j + m))" 
                "p i' \<notin> fun_poss (t j)" 
                unfolding first IH[symmetric]
                unfolding narr_def by (auto simp: jm)
              from narrow_instance_pos_in_subst[OF *[unfolded lri(1)] lri(2) lint lri(3)] 
              show ?thesis unfolding first by auto
            qed
          qed
          thus ?thesis unfolding id1 id2 by auto
        qed
      qed
    qed
  }
  hence "\<forall> ik. \<exists> \<gamma>. fst ik \<le> m \<longrightarrow> t' (fst ik) (snd ik) \<cdot> \<gamma> = t' (fst ik) (Suc (snd ik))" by blast
  from choice[OF this] obtain \<gamma> where 
    "\<And> ik. fst ik \<le> m \<Longrightarrow> t' (fst ik) (snd ik) \<cdot> (\<gamma> ik) = t' (fst ik) (Suc (snd ik))" by blast

  (* the t' i k will increase in k by addition substitions gamma(i,k) *)
  hence t'_mono: "\<And> i k. i \<le> m \<Longrightarrow> t' i (Suc k) = t' i k \<cdot> \<gamma> (i,k)" by auto

  define fp where "fp i k = poss (u i) \<inter> fun_poss (t' i k)" for i k
  define pp where "pp i k = poss (u i) \<inter> poss (t' i k)" for i k
  define vp where "vp i k = poss (u i) \<inter> var_poss (t' i k)" for i k
  {
    fix i
    assume i: "i \<le> m" 
    define meas where "meas k = card (poss (u i) - fun_poss (t' i k)) + card (poss (u i) - poss (t' i k))" for k
    have fp_sub: "fun_poss (t' i k) \<subseteq> fun_poss (t' i (Suc k))" for k
      using t'_mono[OF i, of k] fun_poss_subst_sub by metis
    have pp_sub: "poss (t' i k) \<subseteq> poss (t' i (Suc k))" for k 
      using t'_mono[OF i, of k] by (metis poss_imp_subst_poss subsetI)
    {
      fix k
      have "meas (Suc k) \<le> meas k" unfolding meas_def
      proof (intro add_mono card_mono)
        show "poss (u i) - fun_poss (t' i (Suc k)) \<subseteq> poss (u i) - fun_poss (t' i k)" 
          using fp_sub[of k] by auto
        show "finite (poss (u i) - fun_poss (t' i k))" using finite_poss[of "u i"] by auto
        show "poss (u i) - poss (t' i (Suc k)) \<subseteq> poss (u i) - poss (t' i k)" 
          using pp_sub[of k] by auto
        show "finite (poss (u i) - poss (t' i k))" using finite_poss[of "u i"] by auto
      qed
    }
    hence "\<exists>k0. \<forall>k\<ge>k0. (meas k, meas (Suc k)) \<in> {(x, y). y \<le> x} - {(x, y). y < x}" 
      by (intro non_strict_ending, insert SN_nat_gt, auto simp: SN_defs)
    then obtain k0 where meas_const: "\<And> k. k \<ge> k0 \<Longrightarrow> meas (Suc k) = meas k" by force
    {
      fix k
      assume "k \<ge> k0" 
      then obtain k' where k: "k = k' + k0" and "k' = k - k0" by auto
      have "fp i k = fp i k0 \<and> pp i k = pp i k0" 
        unfolding k
      proof (induct k')
        case (Suc k')
        (* make smt invocation more readable 
        obtain A A' where A: "fun_poss (t' i (Suc (k' + k0))) = A" "poss (t' i (Suc (k' + k0))) = A'" by auto
        obtain B    where B: "poss (u i) = B" by auto
        obtain C C' where C: "fun_poss (t' i (k' + k0)) = C" "poss (t' i (k' + k0)) = C'" by auto
        *)
        from meas_const[of "k' + k0"] 
        have "meas (Suc (k' + k0)) = meas (k' + k0)" by auto
        from this[unfolded meas_def] fp_sub[of "k' + k0"] pp_sub[of "k' + k0"] finite_poss[of "u i"]
        have "fp i (Suc (k' + k0)) = fp i (k' + k0) \<and> pp i (Suc (k' + k0)) = pp i (k' + k0)" unfolding fp_def pp_def 
         (*  unfolding A B C *)
          by (smt (verit, ccfv_threshold) Diff_Diff_Int Diff_mono Nat.add_diff_assoc 
              add.commute add_diff_cancel_left' card_mono card_seteq finite_Diff le_iff_add subsetI)
        with Suc show ?case by auto
      qed auto
    }
    hence "\<exists> k0. \<forall> k \<ge> k0. fp i k = fp i k0 \<and> pp i k = pp i k0" 
      by blast
  }
  hence "\<forall> i. \<exists> k0. i \<le> m \<longrightarrow> (\<forall> k \<ge> k0. fp i k = fp i k0 \<and> pp i k = pp i k0)" 
    by blast
  from choice[OF this] obtain k0 where 
    k0: "\<And> i k. i \<le> m \<Longrightarrow> k \<ge> k0 i \<Longrightarrow> fp i k = fp i (k0 i) \<and> pp i k = pp i (k0 i)" by blast
  define K0 where "K0 = max_list (map k0 [0..<m])" 
  define VP where "VP i = vp i K0" for i
  define FP where "FP i = fp i K0" for i
  define PP where "PP i = pp i K0" for i
  {
    fix i k
    assume i: "i < m" and k: "k \<ge> K0" 
    hence "k0 i \<in> set (map k0 [0..<m])" by auto
    from max_list[OF this] have K: "K0 \<ge> k0 i" by (auto simp: K0_def)
    from i have i: "i \<le> m" by auto
    from k0[OF this K] have one: "fp i K0 = fp i (k0 i) \<and> pp i K0 = pp i (k0 i)" .
    from k K have "k \<ge> k0 i" by auto
    from k0[OF i this] one 
    have fp: "fp i k = fp i K0" and pp: "pp i k = pp i K0" by auto
    have vp: "vp i k = pp i k - fp i k" for k unfolding vp_def pp_def fp_def
      by (metis Diff_Int_distrib poss_simps(4))
    have vp: "vp i k = vp i K0" unfolding vp fp pp by simp
    note fp pp vp
  } 
  (* (var/fun/all) positions stay constant after K0 *)
  hence K0: 
    "fp i k = FP i" 
    "pp i k = PP i" 
    "vp i k = VP i" 
    if "i < m" "k \<ge> K0" for i k using that unfolding FP_def PP_def VP_def by blast+ 
  {
    fix i
    assume i: "i < m" 
    from cond[OF i, unfolded cond_def]
    have "(u i, u (Suc i)) \<in> rstep_r_p_s (Pn i) (lr i) (p i) (\<tau> i) \<union> rstep_r_p_s R (lr i) (p i) (\<tau> i)" 
      by (auto split: if_splits)
    then obtain l r where *: "p i \<in> poss (u i)" "u i |_ p i = l \<cdot> \<tau> i" and "(l,r) \<in> Pn i \<union> R" 
      unfolding rstep_r_p_s_def' by (cases "lr i", auto)
    with lr0 have "(l,r) \<in> P \<union> R" unfolding Pn_def by (auto split: if_splits)
    with wf have "is_Fun l" unfolding wf_trs_def by force
    with * have "is_Fun (u i |_ p i)" by (cases l, auto)
    with *(1) have "p i \<in> fun_poss (u i)" by (rule poss_is_Fun_fun_poss)
  } note puf = this
  have pu: "p i \<in> poss (u i)" if "i < m" for i using puf[OF that] by (rule fun_poss_imp_poss)

  (* these "a" flags indicate whether position i is eventually activated or not *)
  define a where "a i = (p i \<in> fun_poss (t' i K0))" for i
  {
    fix i k
    assume i: "i < m" and "k \<ge> K0" 
    from K0[OF this] have id: "fp i k = fp i K0" by (auto simp: FP_def)
    have "p i \<in> fun_poss (t' i k) \<longleftrightarrow> p i \<in> fp i k" for k 
      unfolding fp_def using pu[OF i] by auto
    with id have "p i \<in> fun_poss (t' i k) \<longleftrightarrow> a i" unfolding a_def by auto
  } note a = this

  (* inactive variables *)
  define IAV where "IAV i k = (\<lambda> q. the_Var (t' i k |_ q)) ` VP i" for i k
  {
    fix i k x
    assume i: "i < m" and k: "k \<ge> K0" and x: "x \<in> IAV i k" 
    from this[unfolded IAV_def] obtain q where q: "q \<in> VP i" and x: "x = the_Var (t' i k |_ q)" by auto  
    from this(1) K0[OF i k] have "q \<in> vp i k" unfolding VP_def by auto
    from this[unfolded vp_def] have "q \<in> var_poss (t' i k)" by auto
    with x have *: "t' i k |_ q = Var x" "q \<in> poss (t' i k)" using var_poss_iff by force+
    hence "x \<in> vars_term (t' i k)" using vars_term_subt_at by fastforce
  } note IAV_vars = this
    
  {
    fix i k
    assume i: "i < m" and k: "k \<ge> K0"
    hence id: "t' i (Suc k) = t' i k \<cdot> \<gamma> (i, k)" using t'_mono by auto
    have var_subst: "\<gamma> (i,k) ` IAV i k \<subseteq> range Var" 
    proof
      fix s
      assume "s \<in> \<gamma> (i, k) ` IAV i k" 
      then obtain x where "x \<in> IAV i k" and s: "s = \<gamma> (i, k) x" by auto
      from this(1)[unfolded IAV_def] obtain q where q: "q \<in> VP i" and x: "x = the_Var (t' i k |_ q)" by auto  
      from this(1) K0[OF i k] have "q \<in> vp i k" unfolding VP_def by auto
      from this[unfolded vp_def] have "q \<in> var_poss (t' i k)" by auto
      with x have *: "t' i k |_ q = Var x" "q \<in> poss (t' i k)" using var_poss_iff by force+
      from arg_cong[OF *(1), of "\<lambda> t. t \<cdot> \<gamma> (i, k)"] this(2) 
      have **: "t' i (Suc k) |_ q = \<gamma> (i, k) x" unfolding id by auto
      from q K0[OF i, of "Suc k"] k have "q \<in> vp i (Suc k)" unfolding VP_def by auto
      from this[unfolded vp_def] have "q \<in> var_poss (t' i (Suc k))" by auto
      then obtain y where "t' i (Suc k) |_ q = Var y" using var_poss_iff by force
      with ** have "\<gamma> (i, k) x \<in> range Var" by auto
      thus "s \<in> range Var" unfolding s by auto
    qed
    have "inj_on (\<gamma> (i,k)) (IAV i k)"
    proof
      fix y1 y2
      assume y12: "y1 \<in> IAV i k" "y2 \<in> IAV i k" and eq: "\<gamma> (i, k) y1 = \<gamma> (i, k) y2"
      from var_subst y12 eq obtain x where gam: "\<gamma> (i, k) y1 = Var x" "\<gamma> (i, k) y2 = Var x"
        by (cases "\<gamma> (i, k) y1"; cases "\<gamma> (i, k) y2"; auto)
      from IAV_vars[OF i k] y12 have "y1 \<in> vars_term (t' i k)" "y2 \<in> vars_term (t' i k)" by auto
      hence y12: "y1 \<in># vars_term_ms (t' i k)"  "y2 \<in># vars_term_ms (t' i k)" by auto
      show "y1 = y2" 
      proof (rule ccontr)
        assume "\<not> ?thesis"
        with y12 obtain M where [simp]: "vars_term_ms (t' i k) = {# y1, y2 #} + M"
          by (metis insert_DiffM mset_single_cases union_mset_add_mset_left)
        then obtain M' where "vars_term_ms (t' i (Suc k)) = {# x, x #} + M'" unfolding id 
          by (simp add: gam)
        with linear_term_count[OF lint[of "i + (Suc k) * m", folded t'_def], of x] 
        show False by auto
      qed
    qed
    with var_subst have "inj_on (\<gamma> (i,k)) (IAV i k)" and "\<gamma> (i,k) ` IAV i k \<subseteq> range Var" by auto
  } note gamma_var_ren = this

  {
    fix i k
    assume *: "i < m" "k \<ge> K0" "\<not> a i" 
    let ?i = "i + k * m" 
    define C where "C = ctxt_of_pos_term (p i) (u i)" 
    from a[OF *(1-2)] *(3) have pi: "p i \<notin> fun_poss (t' i k)" by auto
    from cond2'[of ?i, folded t'_def] * pi have "\<not> b i" by auto
    with bn *(1) have si: "Suc i < m" 
      using Suc_lessI m_def by blast
    have step: "(u i, u (Suc i)) \<in> rstep_r_p_s (S i) (lr i) (p i) (\<tau> i)" 
      using Rel2[OF *(1), of 0, unfolded v_def Rel2_def] by auto
    from this[unfolded rstep_r_p_s_def'] 
    have ui: "u i = C \<langle> fst (lr i) \<cdot> \<tau> i \<rangle>" "u (Suc i) = C \<langle>snd (lr i) \<cdot> \<tau> i \<rangle>" "p i = hole_pos C" 
      using ctxt_supt_id by (force simp: C_def)+
    {
      fix q
      assume "hole_pos C @ q \<in> var_poss (t' i k)" 
      hence "p i @ q \<in> var_poss (t' i k)" unfolding ui by auto
      with pi have "q = []" by (meson fun_poss_append_poss var_poss_iff)
      hence "q \<in> poss (snd (lr i) \<cdot> \<tau> i) \<longleftrightarrow> q \<in> poss (fst (lr i) \<cdot> \<tau> i)" by simp
    } note step = this
    {
      fix q
      assume "hole_pos C @ q \<in> fun_poss (t' i k)" 
      hence "p i @ q \<in> fun_poss (t' i k)" unfolding ui by auto
      with pi have "q = []" 
        using fun_poss_append_poss' by blast
      hence "q \<in> poss (snd (lr i) \<cdot> \<tau> i) \<longleftrightarrow> q \<in> poss (fst (lr i) \<cdot> \<tau> i)" by simp
    } note step' = this
    from cond2'[of ?i] * pi
    have id1: "t' (Suc i) k = t' i k" by (auto simp: t'_def)
    have "VP (Suc i) = VP i \<longleftrightarrow> vp (Suc i) k = vp i k" using K0(3) * si by auto
    also have "\<dots> \<longleftrightarrow> True" 
      unfolding vp_def id1 unfolding ui poss_ctxt_apply using step by auto
    finally have VP_id: "VP (Suc i) = VP i" by simp  
    have "FP (Suc i) = FP i \<longleftrightarrow> fp (Suc i) k = fp i k" using K0(1) * si by auto
    also have "\<dots> \<longleftrightarrow> True" 
      unfolding fp_def id1 unfolding ui poss_ctxt_apply using step' by auto
    finally have FP_id: "FP (Suc i) = FP i" by simp  
    have IAV_id: "IAV (Suc i) k = IAV i k" unfolding IAV_def id1 VP_id by simp
    from si have "Suc i mod m = Suc i" by auto
    note VP_id FP_id IAV_id this
  } note steps_in_subst_keeps_VP_FP_IAV = this

  (* perhaps relevant for the next steps *)
  thm narrow_instance_pos_in_term

  (* unused part; x should not be the only variable at the redex position, 
     but I guess that one needs all IAV's 
  {
    fix i 
    assume i: "i < m" and "\<not> a i" 
    with a have npi: "p i \<notin> fun_poss (t' i K0)" by auto
    from pu[OF i] match2[OF i, of K0]
    have "p i \<in> poss (t' i K0 \<cdot> \<sigma>' i K0)" by simp
    from poss_subst_choice[OF this] npi obtain x q1 q2 where
      "q1 \<in> poss (t' i K0)" "q2 \<in> poss (\<sigma>' i K0 x)" "t' i K0 |_ q1 = Var x" and pi: "p i = q1 @ q2" 
      unfolding fun_poss_poss by blast
    hence q1: "q1 \<in> var_poss (t' i K0)" using var_poss_iff by blast
    from pu[OF i, unfolded pi] have "q1 \<in> poss (u i)" by auto
    with q1 have "q1 \<in> vp i K0" unfolding vp_def by auto
    with pi have "\<exists> q1 q2. p i = q1 @ q2 \<and> q1 \<in> VP i" unfolding VP_def by blast
  }
  hence "\<forall> i. \<exists> q1 q2. i < m \<longrightarrow> \<not> a i \<longrightarrow> p i = q1 @ q2 \<and> q1 \<in> VP i" by blast
  from choice[OF this] obtain q1 where 
    "\<forall> i. \<exists> q2. i < m \<longrightarrow> \<not> a i \<longrightarrow> p i = q1 i @ q2 \<and> q1 i \<in> VP i" by blast
  from choice[OF this] K0(3) obtain q2 where 
    p_split: "\<And> i. i < m \<Longrightarrow> \<not> a i \<Longrightarrow> p i = q1 i @ q2 i" and
    q1_vp: "\<And> i . i < m \<Longrightarrow> \<not> a i \<Longrightarrow> q1 i \<in> VP i" by blast 
  define x where "x i k = the_Var (t' i k |_ q1 i)" for i k
  {
    fix i k 
    assume "i < m" "k \<ge> K0" "\<not> a i"
    from q1_vp[OF this(1,3)] K0[OF this(1-2)] have "q1 i \<in> var_poss (t' i k)" unfolding vp_def by auto
    then obtain y where "t' i k |_ q1 i = Var y" and q1: "q1 i \<in> poss (t' i k)"
      by (meson var_poss_iff)
    hence subt: "t' i k |_ q1 i = Var (x i k)" unfolding x_def by simp
    hence "x i k \<in> vars_term (t' i k)" using q1 using vars_term_subt_at by force
    note this q1 subt
  }
  note x = this
*)


  oops (* perhaps continue by showing that all a's must be set, since otherwise there would be 
          a shorter loop *)


end
end
