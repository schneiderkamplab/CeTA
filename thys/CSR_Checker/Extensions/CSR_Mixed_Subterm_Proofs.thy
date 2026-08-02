(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Mixed_Subterm_Proofs
  imports CSR_Minimal_CSDP_Proofs
begin

lemma SN_relto_mu_supt_restrict_SN_cssteps:
  assumes wf: "wf_trs R"
  shows "SN (relto (mu_supt_rel \<mu>)
    (restrict_SN ((csstep \<mu> R)\<^sup>*) (csstep \<mu> R)))"
proof (rule ccontr)
  let ?A = "csstep \<mu> R"
  let ?M = "mu_supt_rel \<mu>"
  let ?E = "restrict_SN (?A\<^sup>*) ?A"
  assume not_sn: "\<not> SN (relto ?M ?E)"
  then obtain f where chain: "\<And>i. (f i, f (Suc i)) \<in> relto ?M ?E"
    unfolding SN_defs by blast
  have E_preserves:
    "(x,y) \<in> ?E\<^sup>* \<Longrightarrow> SN_on ?A {x} \<Longrightarrow> SN_on ?A {y}"
    for x y
  proof (induct rule: rtrancl_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    from step.hyps(2) have yz: "(y,z) \<in> ?A\<^sup>*"
      unfolding restrict_SN_def by auto
    from step.hyps(3) step.prems have sn_y: "SN_on ?A {y}" by blast
    show ?case by (rule steps_preserve_SN_on[OF yz sn_y])
  qed
  have E_nonSN_identity:
    "\<not> SN_on ?A {x} \<Longrightarrow> (x,y) \<in> ?E\<^sup>* \<Longrightarrow> y = x"
    for x y
  proof -
    assume not_x: "\<not> SN_on ?A {x}" and xy: "(x,y) \<in> ?E\<^sup>*"
    from xy not_x show "y = x"
  proof (induct rule: rtrancl_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    from step.hyps(3) step.prems have yx: "y = x" by blast
    from step.hyps(2) have "SN_on ?A {y}"
      unfolding restrict_SN_def by auto
    with yx have "SN_on ?A {x}" by simp
    with step.prems have False by contradiction
    then show ?case by blast
  qed
  qed
  show False
  proof (cases "\<exists>i. SN_on ?A {f i}")
    case True
    then obtain i where sn_i: "SN_on ?A {f i}" by blast
    let ?g = "shift f i"
    have g0: "SN_on ?A {?g 0}" using sn_i by simp
    have E_sub: "?E \<subseteq> ?A\<^sup>*"
      unfolding restrict_SN_def by auto
    have E_star_sub: "?E\<^sup>* \<subseteq> ?A\<^sup>*"
      using rtrancl_mono[OF E_sub] by simp
    have macro: "(?g k, ?g (Suc k)) \<in> (?M \<union> ?A)\<^sup>+" for k
    proof -
      from chain[of "k + i"] have rel:
        "(?g k, ?g (Suc k)) \<in> ?E\<^sup>* O ?M O ?E\<^sup>*"
        by simp
      then obtain x y where prefix: "(?g k,x) \<in> ?E\<^sup>*"
        and sub: "(x,y) \<in> ?M" and suffix: "(y,?g (Suc k)) \<in> ?E\<^sup>*"
        by auto
      have prefix': "(?g k,x) \<in> (?M \<union> ?A)\<^sup>*"
        using subsetD[OF E_star_sub prefix]
          rtrancl_mono[of ?A "?M \<union> ?A"] by auto
      have sub': "(x,y) \<in> ?M \<union> ?A" using sub by auto
      have suffix': "(y,?g (Suc k)) \<in> (?M \<union> ?A)\<^sup>*"
        using subsetD[OF E_star_sub suffix]
          rtrancl_mono[of ?A "?M \<union> ?A"] by auto
      have first: "(?g k,y) \<in> (?M \<union> ?A)\<^sup>+"
        by (rule rtrancl_into_trancl1[OF prefix' sub'])
      show ?thesis by (rule trancl_rtrancl_trancl[OF first suffix'])
    qed
    have sn_union: "SN_on (?M \<union> ?A) {?g 0}"
      by (rule SN_on_csstep_imp_SN_on_mu_supt_union[OF wf g0])
    have sn_trancl: "SN_on ((?M \<union> ?A)\<^sup>+) {?g 0}"
      by (rule SN_on_trancl[OF sn_union])
    have g_chain: "chain ((?M \<union> ?A)\<^sup>+) ?g"
      using macro by simp
    from sn_trancl g_chain show False
      unfolding SN_on_def by blast
  next
    case False
    have no_sn: "\<not> SN_on ?A {f i}" for i using False by blast
    have direct: "(f i, f (Suc i)) \<in> ?M" for i
    proof -
      from chain[of i] obtain x y where
        prefix: "(f i,x) \<in> ?E\<^sup>*" and sub: "(x,y) \<in> ?M"
        and suffix: "(y,f (Suc i)) \<in> ?E\<^sup>*" by auto
      from E_nonSN_identity[OF no_sn prefix] have x: "x = f i" .
      have not_y: "\<not> SN_on ?A {y}"
      proof
        assume "SN_on ?A {y}"
        from E_preserves[OF suffix this] no_sn[of "Suc i"]
        show False by contradiction
      qed
      from E_nonSN_identity[OF not_y suffix] have y: "f (Suc i) = y" by simp
      show ?thesis using sub x y by simp
    qed
    have m_chain: "chain ?M f" using direct by simp
    have sn_m: "SN ?M"
      by (rule SN_subset[OF SN_supt], unfold mu_supt_rel_def,
        use mu_supt_imp_supt in blast)
    from sn_m m_chain show False unfolding SN_defs by blast
  qed
qed

fun csr_mixed_sct_index where
  "csr_mixed_sct_index U (Fun (Sharp f) ts) (Suc i) = (i < length ts)"
| "csr_mixed_sct_index U (Fun V ts) (Suc i) =
    (V = U \<and> length ts = 1 \<and> i = 0)"
| "csr_mixed_sct_index U t i = False"

lemma csr_mixed_sct_index_sharp [simp]:
  "csr_mixed_sct_index U (Fun (Sharp f) ts) i = csr_sct_index (Fun (Sharp f) ts) i"
  by (cases i, auto)

lemma csr_mixed_sct_index_U:
  assumes index: "csr_mixed_sct_index U (Fun U ts) i"
    and unsharp: "\<not> is_sharp_lab U"
  shows "i = 1 \<and> length ts = 1"
  using assms by (cases U; cases i; simp_all)

lemma csr_mixed_sct_transition:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and index_t: "csr_mixed_sct_index U t i"
    and shape_s: "csr_u3_mixed_term_shape U s"
    and target_SN: "SN_on (csdp_step Sharp \<mu> R) {t \<cdot> \<sigma>}"
    and steps: "(t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "csr_mixed_sct_index U s i \<and>
    (get_arg t i \<cdot> \<sigma>, get_arg s i \<cdot> \<tau>) \<in>
      restrict_SN ((csstep \<mu> R)\<^sup>*) (csstep \<mu> R) \<union> Id"
proof (cases t)
  case (Var x)
  then show ?thesis using index_t by simp
next
  case (Fun g ts)
  have hidden_case: ?thesis if gU: "g = U"
  proof -
    from csr_mixed_sct_index_U[OF index_t[unfolded Fun gU] unsharp]
    have i: "i = 1" and len: "length ts = 1" by auto
    have steps': "(Fun U (map (\<lambda>u. u \<cdot> \<sigma>) ts), s \<cdot> \<tau>) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
      using steps Fun gU by simp
    from csr_u3_unhiding_csdp_steps_identity[
      OF wf fresh_U unsharp steps']
    have finish: "s \<cdot> \<tau> = Fun U (map (\<lambda>u. u \<cdot> \<sigma>) ts)" by simp
    from shape_s obtain ss where s: "s = Fun U ss"
      unfolding csr_u3_mixed_term_shape_def
      using finish unsharp by (cases U, auto)
    from finish[unfolded s] have maps: "map (\<lambda>u. u \<cdot> \<tau>) ss =
      map (\<lambda>u. u \<cdot> \<sigma>) ts" by simp
    have len_ss: "length ss = 1"
      using arg_cong[OF maps, of length] len by simp
    have args_eq: "get_arg t i \<cdot> \<sigma> = get_arg s i \<cdot> \<tau>"
      using maps len len_ss Fun gU s i by (cases ts; cases ss; auto)
    show ?thesis using s i len_ss args_eq unsharp by (cases U; simp_all)
  qed
  show ?thesis
  proof (cases g)
    case (Sharp f)
    have old_index: "csr_sct_index t i" using index_t Fun Sharp by simp
    have sharp_s: "\<exists>h ss. s = Fun (Sharp h) ss"
    proof -
      have start: "t \<cdot> \<sigma> = Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
        using Fun Sharp by simp
      have undef: "\<not> defined R (Sharp f,length (map (\<lambda>u. u \<cdot> \<sigma>) ts))"
        by (rule fresh_sharp)
      from cssteps_Fun_undefined_root_preserved[OF wf undef steps[unfolded start]]
      obtain us where finish: "s \<cdot> \<tau> = Fun (Sharp f) us" by blast
      from shape_s show ?thesis
        unfolding csr_u3_mixed_term_shape_def
      proof
        assume "\<exists>h ss. s = Fun (Sharp h) ss"
        then show ?thesis .
      next
        assume "\<exists>ss. s = Fun U ss"
        then obtain ss where s: "s = Fun U ss" by blast
        from finish[unfolded s] unsharp show ?thesis
          by (cases U, auto)
      qed
    qed
    have old_index_s: "csr_sct_index s i"
      by (rule csr_sct_index_steps[OF wf fresh_sharp old_index sharp_s steps])
    have trans: "(get_arg t i \<cdot> \<sigma>, get_arg s i \<cdot> \<tau>) \<in>
      restrict_SN ((csstep \<mu> R)\<^sup>*) (csstep \<mu> R) \<union> Id"
      by (rule csr_sct_get_arg_transition[
        OF wf fresh_sharp old_index old_index_s target_SN steps])
    show ?thesis using old_index_s sharp_s trans
      unfolding csr_u3_mixed_term_shape_def by auto
  next
    case (Lab h l)
    have gU: "g = U"
      using index_t Fun Lab by (cases i; simp)
    show ?thesis by (rule hidden_case[OF gU])
  next
    case (FunLab h ls)
    have gU: "g = U"
      using index_t Fun FunLab by (cases i; simp)
    show ?thesis by (rule hidden_case[OF gU])
  next
    case (UnLab h)
    have gU: "g = U"
      using index_t Fun UnLab by (cases i; simp)
    show ?thesis by (rule hidden_case[OF gU])
  qed
qed

lemma csr_mixed_sct_valid_proj:
  assumes valid: "csr_mixed_sct_index U t (Suc (p (the (root t))))"
  shows "proj_term p t = get_arg t (Suc (p (the (root t))))"
proof (cases t)
  case (Var x)
  then show ?thesis using valid by simp
next
  case (Fun f ts)
  have less: "p (f,length ts) < length ts"
    using valid Fun by (cases f; cases U; auto)
  show ?thesis using Fun less by (simp add: Let_def)
qed

lemma csr_mixed_sct_root_transition:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and shape_t: "csr_u3_mixed_term_shape U t"
    and shape_s: "csr_u3_mixed_term_shape U s"
    and steps: "(t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "root s = root t"
proof -
  from shape_t show ?thesis
    unfolding csr_u3_mixed_term_shape_def
  proof
    assume "\<exists>f ts. t = Fun (Sharp f) ts"
    then obtain f ts where t: "t = Fun (Sharp f) ts" by blast
    have start: "t \<cdot> \<sigma> = Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
      using t by simp
    from cssteps_Fun_undefined_root_preserved[
      OF wf fresh_sharp steps[unfolded start]]
    obtain us where finish: "s \<cdot> \<tau> = Fun (Sharp f) us"
      and len_us: "length us = length (map (\<lambda>u. u \<cdot> \<sigma>) ts)" by blast
    from shape_s show ?thesis
      unfolding csr_u3_mixed_term_shape_def
    proof
      assume "\<exists>h ss. s = Fun (Sharp h) ss"
      then obtain h ss where s: "s = Fun (Sharp h) ss" by blast
      from finish[unfolded s] len_us show ?thesis using t s by auto
    next
      assume "\<exists>ss. s = Fun U ss"
      then obtain ss where s: "s = Fun U ss" by blast
      from finish[unfolded s] unsharp show ?thesis by (cases U, auto)
    qed
  next
    assume "\<exists>ts. t = Fun U ts"
    then obtain ts where t: "t = Fun U ts" by blast
    have steps': "(Fun U (map (\<lambda>u. u \<cdot> \<sigma>) ts), s \<cdot> \<tau>) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*" using steps t by simp
    from csr_u3_unhiding_csdp_steps_identity[OF wf fresh_U unsharp steps']
    have finish: "s \<cdot> \<tau> = Fun U (map (\<lambda>u. u \<cdot> \<sigma>) ts)" by simp
    from shape_s obtain ss where s: "s = Fun U ss"
      unfolding csr_u3_mixed_term_shape_def
      using finish unsharp by (cases U, auto)
    from finish[unfolded s] have maps:
      "map (\<lambda>u. u \<cdot> \<tau>) ss = map (\<lambda>u. u \<cdot> \<sigma>) ts" by simp
    have len: "length ss = length ts"
      using arg_cong[OF maps, of length] by simp
    show ?thesis using t s len by simp
  qed
qed

theorem finite_min_csr_dpp_mixed_subterm:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
    and p :: "((('f,'l) lab) proj)"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and shape: "\<forall>(u,v)\<in>P.
      csr_u3_mixed_term_shape U u \<and> csr_u3_mixed_term_shape U v"
    and valid: "\<forall>(u,v)\<in>P.
      csr_mixed_sct_index U u (Suc (p (the (root u)))) \<and>
      csr_mixed_sct_index U v (Suc (p (the (root v))))"
    and deleted: "D \<subseteq> P"
    and strict: "\<forall>(u,v)\<in>D.
      mu_supt \<mu> (proj_term p u) (proj_term p v)"
    and weak: "\<forall>(u,v)\<in>P-D.
      proj_term p u = proj_term p v \<or>
      mu_supt \<mu> (proj_term p u) (proj_term p v)"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P-D) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof (rule ccontr)
  let ?A = "csstep \<mu> R"
  let ?M = "mu_supt_rel \<mu>"
  let ?E = "restrict_SN (?A\<^sup>*) ?A"
  let ?W = "?E \<union> Id"
  let ?S = "relto ?M ?W"
  assume not_fin: "\<not> finite_min_csr_dpp Sharp \<mu> P R"
  from not_finite_min_csr_dpp_obtain_chain[OF not_fin]
  obtain s t \<sigma> where pair: "\<And>k. (s k,t k) \<in> P"
    and target_SN: "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
    and steps: "\<And>k. (t k \<cdot> \<sigma> k,
      s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    by blast
  let ?v = "\<lambda>k. proj_term p (s k) \<cdot> \<sigma> k"
  have between: "(proj_term p (t k) \<cdot> \<sigma> k,
      proj_term p (s (Suc k)) \<cdot> \<sigma> (Suc k)) \<in> ?W" for k
  proof -
    from valid pair[of k] have valid_t:
      "csr_mixed_sct_index U (t k) (Suc (p (the (root (t k)))))" by auto
    from valid pair[of "Suc k"] have valid_s:
      "csr_mixed_sct_index U (s (Suc k))
        (Suc (p (the (root (s (Suc k))))))" by auto
    from shape pair[of k] have shape_t: "csr_u3_mixed_term_shape U (t k)" by auto
    from shape pair[of "Suc k"] have shape_s:
      "csr_u3_mixed_term_shape U (s (Suc k))" by auto
    have roots: "root (s (Suc k)) = root (t k)"
      by (rule csr_mixed_sct_root_transition[
        OF wf fresh_sharp fresh_U unsharp shape_t shape_s steps])
    let ?i = "Suc (p (the (root (t k))))"
    have valid_s_i: "csr_mixed_sct_index U (s (Suc k)) ?i"
      using valid_s roots by simp
    from csr_mixed_sct_transition[
      OF wf fresh_sharp fresh_U unsharp valid_t shape_s target_SN steps]
    have trans: "(get_arg (t k) ?i \<cdot> \<sigma> k,
      get_arg (s (Suc k)) ?i \<cdot> \<sigma> (Suc k)) \<in> ?W" by auto
    have proj_t: "proj_term p (t k) = get_arg (t k) ?i"
      by (rule csr_mixed_sct_valid_proj[where U=U and t="t k" and p=p, OF valid_t])
    have proj_s: "proj_term p (s (Suc k)) = get_arg (s (Suc k))
        (Suc (p (the (root (s (Suc k))))))"
      by (rule csr_mixed_sct_valid_proj[where U=U and t="s (Suc k)" and p=p,
            OF valid_s])
    show ?thesis
      using trans proj_t proj_s roots by simp
  qed
  have strict_step: "(u,v) \<in> D \<Longrightarrow>
      (proj_term p u \<cdot> \<rho>, proj_term p v \<cdot> \<rho>) \<in> ?M"
    for u v \<rho>
    using strict mu_supt_subst unfolding mu_supt_rel_def by blast
  have M_W_S: "?M O ?W \<subseteq> ?S" by regexp
  have W_S_S: "?W O ?S \<subseteq> ?S" by regexp
  have W_union: "?W \<subseteq> ?S \<union> ?W" by blast
  have projected: "(?v k, ?v (Suc k)) \<in> ?S \<union> ?W" for k
  proof (cases "(s k,t k) \<in> D")
    case True
    have first: "(?v k, proj_term p (t k) \<cdot> \<sigma> k) \<in> ?M"
      by (rule strict_step[OF True])
    have in_comp: "(?v k, ?v (Suc k)) \<in> ?M O ?W"
      using first between[of k] by blast
    have "(?v k, ?v (Suc k)) \<in> ?S"
      by (rule subsetD[OF M_W_S in_comp])
    then show ?thesis by simp
  next
    case False
    with pair[of k] have residual: "(s k,t k) \<in> P-D" by auto
    from weak[rule_format, OF residual]
    consider (eq) "proj_term p (s k) = proj_term p (t k)"
      | (sub) "mu_supt \<mu> (proj_term p (s k)) (proj_term p (t k))"
      by blast
    then show ?thesis
    proof cases
      case eq
      have eq_sub: "?v k = proj_term p (t k) \<cdot> \<sigma> k"
        using eq(1) by simp
      have w: "(?v k, ?v (Suc k)) \<in> ?W"
        using eq_sub between[of k] by simp
      show "(?v k, ?v (Suc k)) \<in> ?S \<union> ?W"
        by (rule subsetD[OF W_union w])
    next
      case sub
      have subst_step: "(?v k, proj_term p (t k) \<cdot> \<sigma> k) \<in> ?M"
        using mu_supt_subst[OF sub(1), of "\<sigma> k"] unfolding mu_supt_rel_def by auto
      have in_comp: "(?v k, ?v (Suc k)) \<in> ?M O ?W"
        using subst_step between[of k] by blast
      have "(?v k, ?v (Suc k)) \<in> ?S"
        by (rule subsetD[OF M_W_S in_comp])
      then show "(?v k, ?v (Suc k)) \<in> ?S \<union> ?W" by simp
    qed
  qed
  have proj_chain: "chain (?W \<union> ?S) ?v"
    using projected by (simp add: Un_commute)
  have compat: "?W O ?S \<subseteq> ?S" by (rule W_S_S)
  have sn_S: "SN ?S"
  proof -
    have "?S = relto ?M ?E" by simp
    then show ?thesis using SN_relto_mu_supt_restrict_SN_cssteps[OF wf] by simp
  qed
  have sn_on_S: "SN_on ?S {?v 0}"
    by (rule SN_on_subset2[OF _ sn_S], simp)
  have "\<exists>j. \<forall>k\<ge>j. (?v k, ?v (Suc k)) \<in> ?W - ?S"
    by (rule non_strict_ending[OF proj_chain compat sn_on_S])
  then obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?v k, ?v (Suc k)) \<in> ?W - ?S" by auto
  have pair_tail: "(s (k+j),t (k+j)) \<in> P-D" for k
  proof (rule DiffI)
    show "(s (k+j),t (k+j)) \<in> P" by (rule pair)
    show "(s (k+j),t (k+j)) \<notin> D"
    proof
      assume inD: "(s (k+j),t (k+j)) \<in> D"
      have first: "(?v (k+j), proj_term p (t (k+j)) \<cdot> \<sigma> (k+j)) \<in> ?M"
        by (rule strict_step[OF inD])
      have prefix: "(?v (k+j), ?v (k+j)) \<in> ?W\<^sup>*" by simp
      have suffix: "(proj_term p (t (k+j)) \<cdot> \<sigma> (k+j),
          ?v (Suc (k+j))) \<in> ?W\<^sup>*"
        by (rule r_into_rtrancl, rule between)
      have tail_comp: "(?v (k+j), ?v (Suc (k+j))) \<in> ?M O ?W\<^sup>*"
        by (rule relcompI[OF first suffix])
      have inS: "(?v (k+j), ?v (Suc (k+j))) \<in> ?S"
        by (rule relcompI[OF prefix tail_comp])
      from tail[of "k+j"] inS show False by auto
    qed
  qed
  let ?ss = "shift s j"
  let ?tt = "shift t j"
  let ?\<tau> = "shift \<sigma> j"
  let ?RS = "csdp_step Sharp \<mu> R"
  let ?RP = "csr_min_pair_step Sharp \<mu> (P-D) R"
  let ?rel = "?RS\<^sup>* O ?RP O ?RS\<^sup>*"
  let ?vals = "\<lambda>k. ?ss k \<cdot> ?\<tau> k"
  have rel_step: "(?vals k, ?vals (Suc k)) \<in> ?rel" for k
  proof -
    have pair_k: "(?ss k,?tt k) \<in> P-D" using pair_tail[of k] by simp
    have rr_k: "(?ss k \<cdot> ?\<tau> k, ?tt k \<cdot> ?\<tau> k) \<in> rrstep (P-D)"
      unfolding rrstep_def' by (rule Quasi_Order.mem_rel_ofI, use pair_k in auto)
    have sn_k: "SN_on ?RS {?tt k \<cdot> ?\<tau> k}"
      using target_SN[of "k+j"] by simp
    have min_k: "(?ss k \<cdot> ?\<tau> k, ?tt k \<cdot> ?\<tau> k) \<in> ?RP"
      unfolding csr_min_pair_step_def using rr_k sn_k by auto
    have steps_k: "(?tt k \<cdot> ?\<tau> k, ?ss (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> ?RS\<^sup>*"
      using steps[of "k+j"] by simp
    show ?thesis using min_k steps_k by auto
  qed
  have vals_chain: "chain ?rel ?vals" using rel_step by simp
  have "\<not> SN_on ?rel UNIV"
    by (rule not_SN_onI[OF _ vals_chain], simp)
  moreover from fin have "SN_on ?rel UNIV"
    unfolding finite_min_csr_dpp_def SN_rel_on_def .
  ultimately show False by contradiction
qed

fun csr_mixed_sct_index_check where
  "csr_mixed_sct_index_check U (Fun (Sharp f) ts) i =
    (0 < i \<and> i \<le> length ts)"
| "csr_mixed_sct_index_check U (Fun V ts) i =
    (V = U \<and> length ts = 1 \<and> i = 1)"
| "csr_mixed_sct_index_check U t i = False"

lemma csr_mixed_sct_index_check_iff [simp]:
  "csr_mixed_sct_index_check U t i = csr_mixed_sct_index U t i"
proof (cases t)
  case (Var x)
  then show ?thesis by simp
next
  case (Fun f ts)
  then show ?thesis by (cases f; cases i; simp_all add: Suc_le_eq)
qed

definition csr_mixed_projection_pair_valid where
  "csr_mixed_projection_pair_valid U p lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow>
      csr_u3_mixed_term_check U l \<and> csr_u3_mixed_term_check U r \<and>
      csr_mixed_sct_index_check U l (Suc (p (the (root l)))) \<and>
      csr_mixed_sct_index_check U r (Suc (p (the (root r)))))"

definition csr_mixed_projection_pair_strict where
  "csr_mixed_projection_pair_strict \<mu> p lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow>
      proj_term p r \<in> set (mu_supt_list \<mu> (proj_term p l)))"

definition csr_mixed_projection_pair_weak where
  "csr_mixed_projection_pair_weak \<mu> p lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow> proj_term p l = proj_term p r \<or>
      proj_term p r \<in> set (mu_supt_list \<mu> (proj_term p l)))"

definition csr_mixed_subterm_proc ::
  "('dpp, (('f::{showl, compare_order}, 'l::{showl, compare_order}) lab),
      string) dpp_ops \<Rightarrow>
   (('f, 'l) lab) \<Rightarrow> (('f, 'l) lab) muL \<Rightarrow>
   (('f, 'l) lab) projL \<Rightarrow>
   (((('f, 'l) lab), string) rule \<times>
      ((('f, 'l) lab), string) rseq) list \<Rightarrow>
   ((('f, 'l) lab), string) rules \<Rightarrow> 'dpp \<Rightarrow> 'dpp result"
where
  "csr_mixed_subterm_proc J U \<mu> pL rseq Pr dpp =
    check_return (let
      p = create_proj pL;
      P = dpp_ops.pairs J dpp;
      (ps, pns) = dpp_ops.split_pairs J dpp Pr
      in
      check (rseq = [] \<and>
        list_all (csr_mixed_projection_pair_valid U p) P \<and>
        list_all (csr_mixed_projection_pair_strict \<mu> p) ps \<and>
        list_all (csr_mixed_projection_pair_weak \<mu> p) pns)
        (showsl_lit (STR ''invalid mixed marked/unhiding CSR subterm criterion''))
    ) (dpp_spec.delete_pairs J dpp Pr)"

definition csr_mixed_unhiding_present where
  "csr_mixed_unhiding_present U P = list_ex (\<lambda>(l,r).
    (case root l of Some (f,n) \<Rightarrow> f = U | None \<Rightarrow> False) \<or>
    (case root r of Some (f,n) \<Rightarrow> f = U | None \<Rightarrow> False)) P"
lemma csr_mixed_subterm_proc_sound:
  fixes J :: "('dpp, (('f::{showl, compare_order},
      'l::{showl, compare_order}) lab), string) dpp_ops"
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh_sharp: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined (set (dpp_ops.rules J dpp)) (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and proc: "csr_mixed_subterm_proc J U \<mu> pL rseq Pr dpp = return dpp'"
    and fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  obtain ps pns where split: "split_pairs dpp Pr = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Pr"
    and pns: "set pns = set (pairs dpp) - set Pr" by auto
  let ?p = "create_proj pL"
  note ok = proc[unfolded csr_mixed_subterm_proc_def split Let_def,
    simplified]
  from ok have shape: "\<forall>(u,v)\<in>set (pairs dpp).
      csr_u3_mixed_term_shape U u \<and> csr_u3_mixed_term_shape U v"
    by (auto simp: list_all_iff csr_mixed_projection_pair_valid_def
      intro: csr_u3_mixed_term_check_sound)
  from ok have valid: "\<forall>(u,v)\<in>set (pairs dpp).
      csr_mixed_sct_index U u (Suc (?p (the (root u)))) \<and>
      csr_mixed_sct_index U v (Suc (?p (the (root v))))"
    by (auto simp: list_all_iff csr_mixed_projection_pair_valid_def)
  from ok have strict: "\<forall>(u,v)\<in>set ps.
      mu_supt (mu_of \<mu>) (proj_term ?p u) (proj_term ?p v)"
    by (auto simp: list_all_iff csr_mixed_projection_pair_strict_def)
  from ok have weak: "\<forall>(u,v)\<in>set pns.
      proj_term ?p u = proj_term ?p v \<or>
      mu_supt (mu_of \<mu>) (proj_term ?p u) (proj_term ?p v)"
    by (auto simp: list_all_iff csr_mixed_projection_pair_weak_def)
  from ok have dpp': "dpp' = delete_pairs dpp Pr" by auto
  have sem: "dpp_ops.dpp J (delete_pairs dpp Pr) =
      (NFS dpp, M dpp, set (P dpp) - set Pr,
       set (Pw dpp) - set Pr, set (Q dpp), set (R dpp), set (Rw dpp))"
    by (rule delete_P_Pw_sound)
  have sem': "dpp_ops.dpp J (delete_pairs dpp Pr) =
      (NFS (delete_pairs dpp Pr), M (delete_pairs dpp Pr),
       set (P (delete_pairs dpp Pr)), set (Pw (delete_pairs dpp Pr)),
       set (Q (delete_pairs dpp Pr)), set (R (delete_pairs dpp Pr)),
       set (Rw (delete_pairs dpp Pr)))" by (rule dpp_sound)
  from plain have plain_fields:
      "set (pairs dpp) = set (P dpp)" "set (Pw dpp) = {}"
    unfolding plain_csr_dpp_def using pairs_sound[of dpp] by auto
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Pr"
    using sem sem' dpp' plain_fields pairs_sound[of "delete_pairs dpp Pr"] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using sem sem' dpp' rules_sound[of dpp] rules_sound[of "delete_pairs dpp Pr"] by auto
  have remaining: "set (pairs dpp) - set ps = set (pairs dpp) - set Pr"
    using ps by auto
  have fin_res: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - set ps) (set (rules dpp))"
    using fin pairs' rules' remaining by simp
  show ?thesis
  proof (rule finite_min_csr_dpp_mixed_subterm[
      where D="set ps" and p="?p"])
    show "wf_trs (set (rules dpp))" by (rule wf)
    show "\<And>f n. \<not> defined (set (rules dpp)) (Sharp f,n)"
      by (rule fresh_sharp)
    show "\<And>n. \<not> defined (set (rules dpp)) (U,n)" by (rule fresh_U)
    show "\<not> is_sharp_lab U" by (rule unsharp)
    show "\<forall>(u,v)\<in>set (pairs dpp).
      csr_u3_mixed_term_shape U u \<and> csr_u3_mixed_term_shape U v"
      by (rule shape)
    show "\<forall>(u,v)\<in>set (pairs dpp).
      csr_mixed_sct_index U u (Suc (?p (the (root u)))) \<and>
      csr_mixed_sct_index U v (Suc (?p (the (root v))))" by (rule valid)
    show "set ps \<subseteq> set (pairs dpp)" using ps by auto
    show "\<forall>(u,v)\<in>set ps.
      mu_supt (mu_of \<mu>) (proj_term ?p u) (proj_term ?p v)" by (rule strict)
    show "\<forall>(u,v)\<in>set (pairs dpp) - set ps.
      proj_term ?p u = proj_term ?p v \<or>
      mu_supt (mu_of \<mu>) (proj_term ?p u) (proj_term ?p v)"
      using pns weak ps by auto
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - set ps) (set (rules dpp))" by (rule fin_res)
  qed
qed

end
