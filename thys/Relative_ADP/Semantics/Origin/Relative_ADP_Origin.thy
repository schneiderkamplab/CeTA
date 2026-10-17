theory Relative_ADP_Origin
  imports Relative_ADP_Chain_Dev.Relative_ADP_Chain_Criterion
begin

text \<open>
  Experimental origin-flow layer for the hard direction of the IJCAR 2024
  relative ADP chain criterion.  This remains a thin child theory until its API
  is stable.
\<close>

lemma var_poss_erase_adp_term [simp]:
  "var_poss (erase_adp_term t) = var_poss t"
  by (induct t) auto

lemma var_poss_annotate_term [simp]:
  "var_poss (annotate_term A t) = var_poss t"
proof (rule trans)
  show "var_poss (annotate_term A t) =
      var_poss (erase_adp_term (annotate_term A t))"
    by (rule sym, rule var_poss_erase_adp_term)
  show "var_poss (erase_adp_term (annotate_term A t)) = var_poss t"
    by (simp only: erase_annotate_term)
qed

lemma poss_annotate_term_at [simp]:
  "poss (annotate_term_at A p t) = poss t"
proof -
  have "poss (annotate_term_at A p t) =
      poss (erase_adp_term (annotate_term_at A p t))"
    by (rule sym, rule poss_erase_adp_term)
  then show ?thesis by (simp only: erase_annotate_term_at)
qed

lemma annotate_terms_at_nth:
  assumes i: "i < length ts"
  shows "annotate_terms_at A p j ts ! i =
    annotate_term_at A (p @ [j + i]) (ts ! i)"
  using i
proof (induct ts arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc k)
    with Cons.prems have k: "k < length ts" by simp
    show ?thesis
      unfolding Suc
      using Cons.hyps[OF k, of "Suc j"] by simp
  qed
qed

lemma length_annotate_terms_at [simp]:
  "length (annotate_terms_at A p j ts) = length ts"
  by (induct ts arbitrary: p j) auto

lemma sharp_positions_annotate_term_at:
  assumes q: "q \<in> fun_poss t"
  shows "(q \<in> sharp_positions (annotate_term_at A p t)) \<longleftrightarrow>
    p @ q \<in> A"
  using q
proof (induct q arbitrary: p t)
  case Nil
  then show ?case
    by (cases t) (auto simp: sharp_positions_def)
next
  case (Cons i q)
  then obtain f ts where t: "t = Fun f ts"
    by (cases t) auto
  from Cons.prems[unfolded t] have i: "i < length ts"
    and q: "q \<in> fun_poss (ts ! i)" by auto
  have nth:
    "annotate_terms_at A p 0 ts ! i =
      annotate_term_at A (p @ [i]) (ts ! i)"
    using annotate_terms_at_nth[OF i, of A p 0] by simp
  show ?case
    unfolding t
    using i q Cons.hyps[OF q, of "p @ [i]"] nth
    by (auto simp: sharp_positions_def)
qed

lemma sharp_positions_annotate_term:
  assumes q: "q \<in> fun_poss t"
  shows "(q \<in> sharp_positions (annotate_term A t)) \<longleftrightarrow> q \<in> A"
  unfolding annotate_term_def
  using sharp_positions_annotate_term_at[OF q, of A "[]"] by simp

lemma adp_defined_positions_fun_poss:
  "adp_defined_positions D t \<subseteq> fun_poss t"
proof
  fix q
  assume q: "q \<in> adp_defined_positions D t"
  then obtain f ts where q_poss: "q \<in> poss t" and at: "t |_ q = Fun f ts"
    unfolding adp_defined_positions_def by blast
  show "q \<in> fun_poss t"
    by (rule poss_is_Fun_fun_poss[OF q_poss]) (simp add: at)
qed

lemma fun_poss_subst:
  assumes q: "q \<in> fun_poss t"
  shows "q \<in> fun_poss (t \<cdot> sigma)"
proof -
  from fun_poss_fun_conv[OF q] obtain f ts where at: "t |_ q = Fun f ts" by blast
  have q_poss: "q \<in> poss t" by (rule fun_poss_imp_poss[OF q])
  have q_subst: "q \<in> poss (t \<cdot> sigma)" by (rule poss_imp_subst_poss[OF q_poss])
  have at_subst: "(t \<cdot> sigma) |_ q = Fun f (map (\<lambda>u. u \<cdot> sigma) ts)"
    using subt_at_subst[OF q_poss] unfolding at by simp
  have "is_Fun ((t \<cdot> sigma) |_ q)" by (simp add: at_subst)
  then show ?thesis by (rule poss_is_Fun_fun_poss[OF q_subst])
qed

lemma sharp_positions_replace_at_append:
  assumes p: "p \<in> poss s"
    and q: "q \<in> sharp_positions u"
  shows "p @ q \<in> sharp_positions (replace_at s p u)"
proof -
  from q have q_poss: "q \<in> poss u"
    and q_sharp:
      "case root (u |_ q) of None \<Rightarrow> False
       | Some (f, _) \<Rightarrow> is_sharp_symbol f"
    unfolding sharp_positions_def by auto
  have p_after: "p \<in> poss (replace_at s p u)"
    by (rule replace_at_below_poss[OF p]) simp
  have pq_after: "p @ q \<in> poss (replace_at s p u)"
    by (rule pos_append_poss[OF p_after])
       (use q_poss replace_at_subt_at[OF p] in simp)
  have at:
    "replace_at s p u |_ (p @ q) = u |_ q"
    using subt_at_append[OF p_after, of q] replace_at_subt_at[OF p] by simp
  show ?thesis
    unfolding sharp_positions_def
    using pq_after q_sharp at by simp
qed

lemma sharp_positions_below_iff:
  assumes p: "p \<in> poss s"
  shows "(p @ q \<in> sharp_positions s) \<longleftrightarrow>
    q \<in> sharp_positions (s |_ p)"
  unfolding sharp_positions_def
  using p subt_at_append[OF p, of q] by simp

lemma root_subt_replace_strict_below:
  assumes qd: "q @ d \<in> poss s"
    and d: "d \<noteq> []"
  shows "root (replace_at s (q @ d) u |_ q) = root (s |_ q)"
  using qd d
proof (induct q arbitrary: s)
  case Nil
  then show ?case by (cases s; cases d) auto
next
  case (Cons i q)
  then obtain f ts where s: "s = Fun f ts" and i: "i < length ts"
    and qd': "q @ d \<in> poss (ts ! i)"
    by (cases s) auto
  from Cons.hyps[OF qd' Cons.prems(2)]
  show ?case unfolding s using i by (simp add: nth_append)
qed

lemma sharp_positions_replace_outside:
  assumes q: "q \<in> sharp_positions s"
    and p: "p \<in> poss s"
    and outside: "q <\<^sub>p p \<or> q \<bottom> p"
  shows "q \<in> sharp_positions (replace_at s p u)"
proof -
  from q have q_poss: "q \<in> poss s"
    and q_sharp:
      "case root (s |_ q) of None \<Rightarrow> False
       | Some (f, _) \<Rightarrow> is_sharp_symbol f"
    unfolding sharp_positions_def by auto
  from outside show ?thesis
  proof
    assume above: "q <\<^sub>p p"
    then obtain d where pd: "p = q @ d" and d: "d \<noteq> []"
      unfolding less_pos_def' by blast
    have q_after: "q \<in> poss (replace_at s p u)"
      by (rule replace_at_below_poss[OF p])
         (use above in \<open>simp add: prefix_order.strict_implies_order\<close>)
    have root:
      "root (replace_at s p u |_ q) = root (s |_ q)"
      unfolding pd by (rule root_subt_replace_strict_below[OF p[unfolded pd] d])
    show ?thesis
      unfolding sharp_positions_def using q_after q_sharp root by simp
  next
    assume parallel: "q \<bottom> p"
    have q_after: "q \<in> poss (replace_at s p u)"
      using parallel_poss_replace_at[OF parallel_pos_sym[OF parallel] p] q_poss by simp
    have at: "replace_at s p u |_ q = s |_ q"
      by (rule parallel_replace_at_subt_at[OF parallel_pos_sym[OF parallel] p q_poss])
    show ?thesis
      unfolding sharp_positions_def using q_after q_sharp at by simp
  qed
qed

lemma replacement_defined_position_origin:
  assumes p: "p \<in> poss s"
    and q: "q \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    and below: "p \<le>\<^sub>p q"
  obtains a where
    "q = p @ a"
    "a \<in> adp_defined_positions D r"
  | x alpha beta where
    "q = p @ alpha @ beta"
    "alpha \<in> var_poss r"
    "r |_ alpha = Var x"
    "beta \<in> fun_poss (sigma x)"
proof -
  from prefixE[OF below] obtain a where qa: "q = p @ a" by blast
  from q obtain f ts where q_poss:
      "q \<in> poss (replace_at s p (r \<cdot> sigma))"
    and q_at: "replace_at s p (r \<cdot> sigma) |_ q = Fun f ts"
    and fD: "f \<in> D"
    unfolding adp_defined_positions_def by blast
  have p_after: "p \<in> poss (replace_at s p (r \<cdot> sigma))"
    by (rule replace_at_below_poss[OF p]) simp
  have a_poss: "a \<in> poss (r \<cdot> sigma)"
    using q_poss unfolding qa
    by (simp add: subt_at_append[OF p_after] replace_at_subt_at[OF p])
  have a_at: "(r \<cdot> sigma) |_ a = Fun f ts"
    using q_at unfolding qa
    by (simp add: subt_at_append[OF p_after] replace_at_subt_at[OF p])
  from poss_subst_choice[OF a_poss]
  show thesis
  proof
    assume skeleton: "a \<in> poss r \<and> is_Fun (r |_ a)"
    then obtain g us where r_at: "r |_ a = Fun g us"
      by (cases "r |_ a") auto
    have subst_at: "(r \<cdot> sigma) |_ a = (r |_ a) \<cdot> sigma"
      by (rule subt_at_subst[OF skeleton[THEN conjunct1]])
    from subst_at a_at r_at have "g = f" by simp
    with skeleton fD r_at have "a \<in> adp_defined_positions D r"
      unfolding adp_defined_positions_def by blast
    with qa show thesis by (rule that(1))
  next
    assume "\<exists>x alpha beta.
      alpha \<in> poss r \<and>
      beta \<in> poss (sigma x) \<and>
      r |_ alpha = Var x \<and>
      x \<in> vars_term r \<and>
      a = alpha @ beta \<and>
      r \<cdot> sigma |_ a = sigma x |_ beta"
    then obtain x alpha beta where
      alpha_poss: "alpha \<in> poss r"
      and beta_poss: "beta \<in> poss (sigma x)"
      and alpha_at: "r |_ alpha = Var x"
      and a: "a = alpha @ beta"
      and subst_at: "r \<cdot> sigma |_ a = sigma x |_ beta"
      by blast
    have alpha_var: "alpha \<in> var_poss r"
      unfolding var_poss_iff using alpha_poss alpha_at by blast
    have beta_fun: "beta \<in> fun_poss (sigma x)"
      by (rule poss_is_Fun_fun_poss[OF beta_poss])
         (use subst_at a_at in simp)
    show thesis
      by (rule that(2)[OF _ alpha_var alpha_at beta_fun])
         (simp add: qa a)
  qed
qed

lemma annotate_term_at_variable_position:
  assumes q: "q \<in> var_poss t"
  shows "annotate_term A t |_ q = plain_adp_term t |_ q"
proof -
  from q obtain x where tq: "t |_ q = Var x"
    unfolding var_poss_iff by blast
  have q_plain: "q \<in> poss (plain_adp_term t)"
    using q by (simp add: var_poss_imp_poss)
  have q_ann: "q \<in> poss (annotate_term A t)"
    using q by (simp add: var_poss_imp_poss)
  have erased:
    "erase_adp_term (annotate_term A t |_ q) = t |_ q"
    using erase_adp_term_subt_at[OF q_ann] by simp
  have plain:
    "plain_adp_term t |_ q = plain_adp_term (t |_ q)"
    using plain_adp_term_subt_at[of q t] q by (simp add: var_poss_imp_poss)
  show ?thesis
    using erased plain unfolding tq
    by (cases "annotate_term A t |_ q") auto
qed

lemma covering_vrf_valid_annotated_rhs:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
  shows "valid_vrf (plain_adp_term l, annotate_term C r) (covering_vrf l r)"
  unfolding valid_vrf_def fst_conv snd_conv
proof (intro ballI)
  fix p
  assume p: "p \<in> var_poss (plain_adp_term l)"
  then have p': "p \<in> var_poss l" by simp
  show "case covering_vrf l r p of None \<Rightarrow> True
      | Some q \<Rightarrow>
          q \<in> var_poss (annotate_term C r) \<and>
          plain_adp_term l |_ p = annotate_term C r |_ q"
  proof (cases "covering_vrf l r p")
    case None
    then show ?thesis by simp
  next
    case (Some q)
    from covering_vrf_at_lhs_position[OF nd p'] Some
    have q: "q \<in> var_poss r"
      and eq: "plain_adp_term l |_ p = plain_adp_term r |_ q"
      by auto
    show ?thesis
      unfolding Some
      using q eq annotate_term_at_variable_position[OF q] by simp
  qed
qed

lemma valid_vrf_annotated_rhs:
  assumes valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
  shows "valid_vrf (plain_adp_term l, annotate_term C r) phi"
  unfolding valid_vrf_def fst_conv snd_conv
proof (intro ballI)
  fix p
  assume p: "p \<in> var_poss (plain_adp_term l)"
  have valid_p:
    "case phi p of None \<Rightarrow> True
     | Some q \<Rightarrow>
         q \<in> var_poss (plain_adp_term r) \<and>
         plain_adp_term l |_ p = plain_adp_term r |_ q"
  proof -
    from valid have
      "\<forall>p \<in> var_poss (plain_adp_term l).
        case phi p of None \<Rightarrow> True
        | Some q \<Rightarrow>
            q \<in> var_poss (plain_adp_term r) \<and>
            plain_adp_term l |_ p = plain_adp_term r |_ q"
      using valid unfolding valid_vrf_def
      by (simp only: fst_conv snd_conv)
    then show ?thesis using p by blast
  qed
  show "case phi p of None \<Rightarrow> True
      | Some q \<Rightarrow>
          q \<in> var_poss (annotate_term C r) \<and>
          plain_adp_term l |_ p = annotate_term C r |_ q"
  proof (cases "phi p")
    case None
    then show ?thesis by simp
  next
    case (Some q)
    then have q: "q \<in> var_poss (plain_adp_term r)"
      and eq: "plain_adp_term l |_ p = plain_adp_term r |_ q"
      using valid_p by auto
    have qr: "q \<in> var_poss r" using q by simp
    show ?thesis
      unfolding Some
      using qr eq annotate_term_at_variable_position[OF qr] by simp
  qed
qed

lemma empty_vrf_valid:
  "valid_vrf adp (\<lambda>_. None)"
  unfolding valid_vrf_def by simp

definition singleton_vrf :: "pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> pos option" where
  "singleton_vrf rho alpha p = (if p = rho then Some alpha else None)"

lemma singleton_vrf_valid:
  assumes rho: "rho \<in> var_poss l"
    and alpha: "alpha \<in> var_poss r"
    and same: "l |_ rho = r |_ alpha"
  shows "valid_vrf (plain_adp_term l, plain_adp_term r)
    (singleton_vrf rho alpha)"
  unfolding valid_vrf_def fst_conv snd_conv
proof (intro ballI)
  fix p
  assume p: "p \<in> var_poss (plain_adp_term l)"
  show "case singleton_vrf rho alpha p of None \<Rightarrow> True
      | Some q \<Rightarrow>
          q \<in> var_poss (plain_adp_term r) \<and>
          plain_adp_term l |_ p = plain_adp_term r |_ q"
  proof (cases "p = rho")
    case False
    then show ?thesis by (simp add: singleton_vrf_def)
  next
    case True
    have rho_poss: "rho \<in> poss l" by (rule var_poss_imp_poss[OF rho])
    have alpha_poss: "alpha \<in> poss r" by (rule var_poss_imp_poss[OF alpha])
    show ?thesis
      unfolding singleton_vrf_def True if_True
      using alpha same plain_adp_term_subt_at[OF rho_poss]
        plain_adp_term_subt_at[OF alpha_poss]
      by simp
  qed
qed

lemma plain_adp_term_pred_plain [simp]:
  "plain_adp_term_pred (plain_adp_term t)"
  by (induct t) (auto simp: list_all_iff)

lemma canonical_nonduplicating_step:
  assumes rule: "(l, r) \<in> R"
    and targets: "origin_root_targets n D r A"
    and nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> fun_poss s"
    and redex: "erase_adp_term (s |_ p) = l \<cdot> sigma"
  obtains C t where
    "A \<subseteq> C"
    "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    "adp_step_case (canonical_adps n D R) (p \<in> sharp_positions s) s t"
    "p \<in> sharp_positions s \<longrightarrow>
      (\<forall>q \<in> A. p @ q \<in> sharp_positions t)"
    "\<forall>q. q \<in> sharp_positions s \<longrightarrow>
      (q <\<^sub>p p \<or> q \<bottom> p) \<longrightarrow>
      q \<in> sharp_positions t"
    "\<forall>rho alpha beta.
      rho \<in> var_poss l \<longrightarrow>
      covering_vrf l r rho = Some alpha \<longrightarrow>
      p @ rho @ beta \<in> sharp_positions s \<longrightarrow>
      alpha @ beta \<in> fun_poss (r \<cdot> sigma) \<longrightarrow>
      p @ alpha @ beta \<in> sharp_positions t"
proof -
  obtain C where AC: "A \<subseteq> C" and CU: "C \<subseteq> adp_defined_positions D r"
    and cardC: "card C = min n (card (adp_defined_positions D r))"
    using origin_root_targets_extend[OF targets] by blast
  have adp: "(plain_adp_term l, annotate_term C r) \<in> canonical_adps n D R"
    using rule CU cardC unfolding canonical_adps_def by blast
  let ?phi = "covering_vrf l r"
  let ?at = "p \<in> sharp_positions s"
  let ?B = "(if ?at then sharp_positions (annotate_term C r) else {}) \<union>
    transported_annotations ?phi (plain_adp_term l) (s |_ p)"
  let ?t = "replace_at s p
    (annotate_term ?B (erase_adp_term (annotate_term C r) \<cdot> sigma))"
  have step:
    "adp_step_case (canonical_adps n D R) ?at s ?t"
    by (rule adp_step_case.adp_stepI[
          where l = "plain_adp_term l" and r = "annotate_term C r"
            and phi = ?phi and p = p and sigma = sigma and A = ?B,
          OF adp plain_adp_term_pred_plain[of l]
            covering_vrf_valid_annotated_rhs[OF nd, where C = C] p refl])
       (use redex in auto)
  have p_poss: "p \<in> poss s" using p by (rule fun_poss_imp_poss)
  have erased:
    "erase_adp_term ?t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    using p_poss by simp
  have marked:
    "?at \<longrightarrow> (\<forall>q \<in> A. p @ q \<in> sharp_positions ?t)"
  proof (intro impI ballI)
    fix q
    assume at: ?at and qA: "q \<in> A"
    have qC: "q \<in> C" using AC qA by blast
    have q_fun: "q \<in> fun_poss r"
      using adp_defined_positions_fun_poss CU qC by blast
    have q_rhs_sharp: "q \<in> sharp_positions (annotate_term C r)"
      using sharp_positions_annotate_term[OF q_fun] qC by simp
    have q_subst_fun: "q \<in> fun_poss (r \<cdot> sigma)"
      by (rule fun_poss_subst[OF q_fun])
    have qB: "q \<in> ?B" using at q_rhs_sharp by simp
    have "q \<in> sharp_positions (annotate_term ?B (r \<cdot> sigma))"
      using sharp_positions_annotate_term[OF q_subst_fun] qB by simp
    then show "p @ q \<in> sharp_positions ?t"
      using sharp_positions_replace_at_append[OF p_poss] by simp
  qed
  have transported:
    "\<forall>rho alpha beta.
      rho \<in> var_poss l \<longrightarrow>
      ?phi rho = Some alpha \<longrightarrow>
      p @ rho @ beta \<in> sharp_positions s \<longrightarrow>
      alpha @ beta \<in> fun_poss (r \<cdot> sigma) \<longrightarrow>
      p @ alpha @ beta \<in> sharp_positions ?t"
  proof (intro allI impI)
    fix rho alpha beta
    assume rho: "rho \<in> var_poss l"
      and phi: "?phi rho = Some alpha"
      and source: "p @ rho @ beta \<in> sharp_positions s"
      and target_fun: "alpha @ beta \<in> fun_poss (r \<cdot> sigma)"
    have local_source: "rho @ beta \<in> sharp_positions (s |_ p)"
      using source sharp_positions_below_iff[OF p_poss, of "rho @ beta"] by simp
    have in_transport:
      "alpha @ beta \<in>
        transported_annotations ?phi (plain_adp_term l) (s |_ p)"
      unfolding transported_annotations_def
      using rho phi local_source by force
    have in_B: "alpha @ beta \<in> ?B" using in_transport by simp
    have "alpha @ beta \<in>
      sharp_positions (annotate_term ?B (r \<cdot> sigma))"
      using sharp_positions_annotate_term[OF target_fun] in_B by simp
    then show "p @ alpha @ beta \<in> sharp_positions ?t"
      using sharp_positions_replace_at_append[OF p_poss] by simp
  qed
  have outside:
    "\<forall>q. q \<in> sharp_positions s \<longrightarrow>
      (q <\<^sub>p p \<or> q \<bottom> p) \<longrightarrow>
      q \<in> sharp_positions ?t"
    by (intro allI impI, rule sharp_positions_replace_outside[OF _ p_poss])
       assumption+
  show thesis by (rule that[OF AC erased step marked outside transported])
qed

lemma canonical_strict_step:
  assumes rule: "(l, r) \<in> R"
    and targets: "origin_root_targets n D r A"
    and vrf: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and p: "p \<in> fun_poss s"
    and redex: "erase_adp_term (s |_ p) = l \<cdot> sigma"
  obtains C t where
    "A \<subseteq> C"
    "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    "adp_step_case (canonical_adps n D R) (p \<in> sharp_positions s) s t"
    "p \<in> sharp_positions s \<longrightarrow>
      (\<forall>q \<in> A. p @ q \<in> sharp_positions t)"
    "\<forall>q. q \<in> sharp_positions s \<longrightarrow>
      (q <\<^sub>p p \<or> q \<bottom> p) \<longrightarrow>
      q \<in> sharp_positions t"
    "\<forall>rho alpha beta.
      rho \<in> var_poss l \<longrightarrow>
      phi rho = Some alpha \<longrightarrow>
      p @ rho @ beta \<in> sharp_positions s \<longrightarrow>
      alpha @ beta \<in> fun_poss (r \<cdot> sigma) \<longrightarrow>
      p @ alpha @ beta \<in> sharp_positions t"
proof -
  obtain C where AC: "A \<subseteq> C" and CU: "C \<subseteq> adp_defined_positions D r"
    and cardC: "card C = min n (card (adp_defined_positions D r))"
    using origin_root_targets_extend[OF targets] by blast
  have adp: "(plain_adp_term l, annotate_term C r) \<in> canonical_adps n D R"
    using rule CU cardC unfolding canonical_adps_def by blast
  let ?phi = phi
  let ?at = "p \<in> sharp_positions s"
  let ?B = "(if ?at then sharp_positions (annotate_term C r) else {}) \<union>
    transported_annotations ?phi (plain_adp_term l) (s |_ p)"
  let ?t = "replace_at s p
    (annotate_term ?B (erase_adp_term (annotate_term C r) \<cdot> sigma))"
  have step:
    "adp_step_case (canonical_adps n D R) ?at s ?t"
    by (rule adp_step_case.adp_stepI[
          where l = "plain_adp_term l" and r = "annotate_term C r"
            and phi = ?phi and p = p and sigma = sigma and A = ?B,
          OF adp plain_adp_term_pred_plain[of l]
            valid_vrf_annotated_rhs[OF vrf, where C = C] p refl])
       (use redex in auto)
  have p_poss: "p \<in> poss s" using p by (rule fun_poss_imp_poss)
  have erased:
    "erase_adp_term ?t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    using p_poss by simp
  have marked:
    "?at \<longrightarrow> (\<forall>q \<in> A. p @ q \<in> sharp_positions ?t)"
  proof (intro impI ballI)
    fix q
    assume at: ?at and qA: "q \<in> A"
    have qC: "q \<in> C" using AC qA by blast
    have q_fun: "q \<in> fun_poss r"
      using adp_defined_positions_fun_poss CU qC by blast
    have q_rhs_sharp: "q \<in> sharp_positions (annotate_term C r)"
      using sharp_positions_annotate_term[OF q_fun] qC by simp
    have q_subst_fun: "q \<in> fun_poss (r \<cdot> sigma)"
      by (rule fun_poss_subst[OF q_fun])
    have qB: "q \<in> ?B" using at q_rhs_sharp by simp
    have "q \<in> sharp_positions (annotate_term ?B (r \<cdot> sigma))"
      using sharp_positions_annotate_term[OF q_subst_fun] qB by simp
    then show "p @ q \<in> sharp_positions ?t"
      using sharp_positions_replace_at_append[OF p_poss] by simp
  qed
  have outside:
    "\<forall>q. q \<in> sharp_positions s \<longrightarrow>
      (q <\<^sub>p p \<or> q \<bottom> p) \<longrightarrow>
      q \<in> sharp_positions ?t"
    by (intro allI impI, rule sharp_positions_replace_outside[OF _ p_poss])
       assumption+
  have transported:
    "\<forall>rho alpha beta.
      rho \<in> var_poss l \<longrightarrow>
      ?phi rho = Some alpha \<longrightarrow>
      p @ rho @ beta \<in> sharp_positions s \<longrightarrow>
      alpha @ beta \<in> fun_poss (r \<cdot> sigma) \<longrightarrow>
      p @ alpha @ beta \<in> sharp_positions ?t"
  proof (intro allI impI)
    fix rho alpha beta
    assume rho: "rho \<in> var_poss l"
      and phi: "?phi rho = Some alpha"
      and source: "p @ rho @ beta \<in> sharp_positions s"
      and target_fun: "alpha @ beta \<in> fun_poss (r \<cdot> sigma)"
    have local_source: "rho @ beta \<in> sharp_positions (s |_ p)"
      using source sharp_positions_below_iff[OF p_poss, of "rho @ beta"] by simp
    have in_transport:
      "alpha @ beta \<in>
        transported_annotations ?phi (plain_adp_term l) (s |_ p)"
      unfolding transported_annotations_def
      using rho phi local_source by force
    have in_B: "alpha @ beta \<in> ?B" using in_transport by simp
    have "alpha @ beta \<in>
      sharp_positions (annotate_term ?B (r \<cdot> sigma))"
      using sharp_positions_annotate_term[OF target_fun] in_B by simp
    then show "p @ alpha @ beta \<in> sharp_positions ?t"
      using sharp_positions_replace_at_append[OF p_poss] by simp
  qed
  show thesis by (rule that[OF AC erased step marked outside transported])
qed

inductive origin_edge ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow>
    ('v \<Rightarrow> ('f, 'v) term) \<Rightarrow> pos set \<Rightarrow>
    (pos \<Rightarrow> pos option) \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool" where
  preserved:
    "q <\<^sub>p p \<or> q \<bottom> p \<Longrightarrow>
     origin_edge l r p sigma A phi q q"
| root_target:
    "alpha \<in> A \<Longrightarrow>
     origin_edge l r p sigma A phi p (p @ alpha)"
| variable_transport:
    "rho \<in> var_poss l \<Longrightarrow>
     phi rho = Some alpha \<Longrightarrow>
     alpha @ beta \<in> fun_poss (r \<cdot> sigma) \<Longrightarrow>
     origin_edge l r p sigma A phi
       (p @ rho @ beta) (p @ alpha @ beta)"

lemma canonical_nonduplicating_origin_step:
  assumes rule: "(l, r) \<in> R"
    and targets: "origin_root_targets n D r A"
    and nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> fun_poss s"
    and redex: "erase_adp_term (s |_ p) = l \<cdot> sigma"
  obtains t where
    "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    "adp_step_case (canonical_adps n D R) (p \<in> sharp_positions s) s t"
    "\<forall>q q'. origin_edge l r p sigma A (covering_vrf l r) q q' \<longrightarrow>
      q \<in> sharp_positions s \<longrightarrow> q' \<in> sharp_positions t"
proof (rule canonical_nonduplicating_step[OF rule targets nd p redex])
  fix C t
  assume AC: "A \<subseteq> C"
    and erased: "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    and step: "adp_step_case (canonical_adps n D R)
      (p \<in> sharp_positions s) s t"
    and root: "p \<in> sharp_positions s \<longrightarrow>
      (\<forall>q \<in> A. p @ q \<in> sharp_positions t)"
    and outside: "\<forall>q. q \<in> sharp_positions s \<longrightarrow>
      (q <\<^sub>p p \<or> q \<bottom> p) \<longrightarrow> q \<in> sharp_positions t"
    and transport: "\<forall>rho alpha beta.
      rho \<in> var_poss l \<longrightarrow>
      covering_vrf l r rho = Some alpha \<longrightarrow>
      p @ rho @ beta \<in> sharp_positions s \<longrightarrow>
      alpha @ beta \<in> fun_poss (r \<cdot> sigma) \<longrightarrow>
      p @ alpha @ beta \<in> sharp_positions t"
  have realizes:
    "\<forall>q q'. origin_edge l r p sigma A (covering_vrf l r) q q' \<longrightarrow>
      q \<in> sharp_positions s \<longrightarrow> q' \<in> sharp_positions t"
  proof (intro allI impI)
    fix q q'
    assume edge: "origin_edge l r p sigma A (covering_vrf l r) q q'"
      and marked: "q \<in> sharp_positions s"
    from edge show "q' \<in> sharp_positions t"
    proof cases
      case preserved
      then show ?thesis using outside marked by blast
    next
      case (root_target alpha)
      then show ?thesis using root marked by blast
    next
      case (variable_transport rho alpha beta)
      then show ?thesis using transport marked by blast
    qed
  qed
  show thesis by (rule that[OF erased step realizes])
qed

lemma canonical_strict_origin_step:
  assumes rule: "(l, r) \<in> R"
    and targets: "origin_root_targets n D r A"
    and vrf: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and p: "p \<in> fun_poss s"
    and redex: "erase_adp_term (s |_ p) = l \<cdot> sigma"
  obtains t where
    "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    "adp_step_case (canonical_adps n D R) (p \<in> sharp_positions s) s t"
    "\<forall>q q'. origin_edge l r p sigma A phi q q' \<longrightarrow>
      q \<in> sharp_positions s \<longrightarrow> q' \<in> sharp_positions t"
proof (rule canonical_strict_step[OF rule targets vrf p redex])
  fix C t
  assume AC: "A \<subseteq> C"
    and erased: "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    and step: "adp_step_case (canonical_adps n D R)
      (p \<in> sharp_positions s) s t"
    and root: "p \<in> sharp_positions s \<longrightarrow>
      (\<forall>q \<in> A. p @ q \<in> sharp_positions t)"
    and outside: "\<forall>q. q \<in> sharp_positions s \<longrightarrow>
      (q <\<^sub>p p \<or> q \<bottom> p) \<longrightarrow> q \<in> sharp_positions t"
    and transport: "\<forall>rho alpha beta.
      rho \<in> var_poss l \<longrightarrow>
      phi rho = Some alpha \<longrightarrow>
      p @ rho @ beta \<in> sharp_positions s \<longrightarrow>
      alpha @ beta \<in> fun_poss (r \<cdot> sigma) \<longrightarrow>
      p @ alpha @ beta \<in> sharp_positions t"
  have realizes:
    "\<forall>q q'. origin_edge l r p sigma A phi q q' \<longrightarrow>
      q \<in> sharp_positions s \<longrightarrow> q' \<in> sharp_positions t"
  proof (intro allI impI)
    fix q q'
    assume edge: "origin_edge l r p sigma A phi q q'"
      and marked: "q \<in> sharp_positions s"
    from edge show "q' \<in> sharp_positions t"
    proof cases
      case preserved
      then show ?thesis using outside marked by blast
    next
      case (root_target alpha)
      then show ?thesis using root marked by blast
    next
      case (variable_transport rho alpha beta)
      then show ?thesis using transport marked by blast
    qed
  qed
  show thesis by (rule that[OF erased step realizes])
qed

end
