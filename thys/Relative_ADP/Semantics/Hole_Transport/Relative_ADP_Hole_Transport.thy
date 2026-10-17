theory Relative_ADP_Hole_Transport
  imports Relative_ADP_Carrier_Refinement_Dev.Relative_ADP_Carrier_Refinement
begin

lemma context_or_below_hole_disj:
  assumes prefix: "C \<le> mctxt_of_term t"
    and q: "q \<in> poss t"
  shows "q \<in> poss_mctxt C \<or>
    (\<exists>h beta. h \<in> hole_poss C \<and> q = h @ beta)"
  using prefix q
proof (induct C arbitrary: t q)
  case MHole
  then show ?case by auto
next
  case (MVar x)
  then show ?case by (cases t) (auto elim: less_eq_mctxtE2)
next
  case (MFun f Cs)
  from MFun.prems(1) obtain ts where t: "t = Fun f ts"
    and length: "length Cs = length ts"
    and child: "\<And>i. i < length Cs \<Longrightarrow>
      Cs ! i \<le> mctxt_of_term (ts ! i)"
    by (cases t) (auto elim: less_eq_mctxtE2)
  show ?case
  proof (cases q)
    case Nil
    then show ?thesis by simp
  next
    case (Cons i q')
    from MFun.prems(2)[unfolded t Cons] have i: "i < length ts"
      and q': "q' \<in> poss (ts ! i)" by auto
    have iC: "i < length Cs" using i length by simp
    from MFun.hyps[OF nth_mem[OF iC] child[OF iC] q']
    show ?thesis
    proof
      assume retained: "q' \<in> poss_mctxt (Cs ! i)"
      then show ?thesis unfolding Cons using iC by auto
    next
      assume "\<exists>h beta. h \<in> hole_poss (Cs ! i) \<and> q' = h @ beta"
      then obtain h beta where h: "h \<in> hole_poss (Cs ! i)"
        and q': "q' = h @ beta" by blast
      have "i # h \<in> hole_poss (MFun f Cs)" using iC h by auto
      moreover have "q = (i # h) @ beta" unfolding Cons q' by simp
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma context_or_below_hole:
  assumes prefix: "C \<le> mctxt_of_term t"
    and q: "q \<in> poss t"
  obtains (retained) "q \<in> poss_mctxt C"
    | (hole) h beta where "h \<in> hole_poss C" "q = h @ beta"
  using context_or_below_hole_disj[OF prefix q] that by blast

lemma hole_pos_mreplace_at_disj:
  assumes p: "p \<in> poss_mctxt C"
    and q: "q \<in> hole_poss (mreplace_at C p E)"
  shows
    "(q \<in> hole_poss C \<and> q \<bottom> p) \<or>
     (\<exists>a. q = p @ a \<and> a \<in> hole_poss E)"
  using assms
proof (induct p arbitrary: C q)
  case Nil
  then show ?case by auto
next
  case (Cons i p)
  from Cons.prems(1) obtain f Cs where C: "C = MFun f Cs"
    and i: "i < length Cs" and p: "p \<in> poss_mctxt (Cs ! i)"
    by (cases C) auto
  have replace:
    "mreplace_at C (i # p) E =
      MFun f (Cs[i := mreplace_at (Cs ! i) p E])"
    unfolding C using i by (simp add: upd_conv_take_nth_drop)
  from Cons.prems(2)[unfolded replace]
  obtain j q' where q: "q = j # q'"
    and j: "j < length Cs"
    and q_hole:
      "q' \<in> hole_poss
        ((Cs[i := mreplace_at (Cs ! i) p E]) ! j)"
    by (auto simp: upd_conv_take_nth_drop)
  show ?case
  proof (cases "j = i")
    case True
    have q_replaced: "q' \<in> hole_poss (mreplace_at (Cs ! i) p E)"
      using q_hole i unfolding True by simp
    from Cons.hyps[OF p q_replaced]
    show ?thesis
    proof
      assume outside: "q' \<in> hole_poss (Cs ! i) \<and> q' \<bottom> p"
      have "q \<in> hole_poss C \<and> q \<bottom> (i # p)"
        unfolding C q True using i outside by auto
      then show ?thesis by blast
    next
      assume inside: "\<exists>a. q' = p @ a \<and> a \<in> hole_poss E"
      then show ?thesis unfolding q True by auto
    qed
  next
    case False
    have q_old: "q' \<in> hole_poss (Cs ! j)"
      using q_hole i j False by simp
    have "q \<in> hole_poss C \<and> q \<bottom> (i # p)"
      unfolding C q using j q_old False by auto
    then show ?thesis by blast
  qed
qed

lemma hole_pos_subm_at_append:
  assumes source: "a \<in> all_poss_mctxt C"
    and hole: "b \<in> hole_poss (subm_at C a)"
  shows "a @ b \<in> hole_poss C"
  using assms
proof (induct a arbitrary: C)
  case Nil
  then show ?case by simp
next
  case (Cons i a)
  from Cons.prems(1) obtain f Cs where C: "C = MFun f Cs"
    and i: "i < length Cs" and a: "a \<in> all_poss_mctxt (Cs ! i)"
    by (cases C) auto
  have "a @ b \<in> hole_poss (Cs ! i)"
    by (rule Cons.hyps[OF a]) (use Cons.prems(2) C in simp)
  then show ?case unfolding C using i by auto
qed

lemma rhs_origin_mctxt_hole:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and C_prefix: "C \<le> mctxt_of_term s"
    and p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and alpha: "alpha \<in> poss r"
    and at: "r |_ alpha = t"
    and hole: "a \<in> hole_poss (rhs_origin_mctxt_at l r p C alpha t)"
  shows
    "(\<exists>gamma beta.
       gamma \<in> var_poss t \<and> a = gamma @ beta \<and>
       p @ rhs_predecessor l r (alpha @ gamma) @ beta \<in> hole_poss C) \<or>
     (\<exists>gamma h beta.
       gamma \<in> var_poss t \<and> a = gamma \<and>
       h \<in> hole_poss C \<and>
       p @ rhs_predecessor l r (alpha @ gamma) = h @ beta)"
  using alpha at hole
proof (induct t arbitrary: alpha a)
  case (Var x)
  have alpha_var: "alpha \<in> var_poss r"
    unfolding var_poss_iff using Var.prems by blast
  let ?rho = "rhs_predecessor l r alpha"
  have rho: "?rho \<in> var_poss l"
    by (rule rhs_predecessor_properties(1)[OF nd alpha_var])
  have rho_poss: "?rho \<in> poss l" by (rule var_poss_imp_poss[OF rho])
  have source_term: "p @ ?rho \<in> poss s"
    using p rho_poss redex by (simp only: poss_append_poss) simp
  show ?case
  proof (cases "p @ ?rho \<in> poss_mctxt C")
    case True
    from Var.prems(3) True have
      a_hole: "a \<in> hole_poss (subm_at C (p @ ?rho))"
      by (simp add: Let_def)
    have source_all: "p @ ?rho \<in> all_poss_mctxt C"
      using True unfolding all_poss_mctxt_conv by blast
    have "p @ ?rho @ a \<in> hole_poss C"
      using hole_pos_subm_at_append[OF source_all a_hole]
      by (simp add: append_assoc)
    have gamma: "[] \<in> var_poss (Var x)" by simp
    have a_eq: "a = [] @ a" by simp
    have source:
      "p @ rhs_predecessor l r (alpha @ []) @ a \<in> hole_poss C"
      using \<open>p @ ?rho @ a \<in> hole_poss C\<close> by simp
    show ?thesis by (rule disjI1) (use gamma a_eq source in blast)
  next
    case False
    have a: "a = []" using Var.prems(3) False by (simp add: Let_def)
    from context_or_below_hole_disj[OF C_prefix source_term]
    show ?thesis
    proof
      assume retained: "p @ ?rho \<in> poss_mctxt C"
      with False show ?thesis by blast
    next
      assume "\<exists>h beta. h \<in> hole_poss C \<and> p @ ?rho = h @ beta"
      then obtain h beta where h: "h \<in> hole_poss C"
        and source: "p @ ?rho = h @ beta" by blast
      show ?thesis
        by (rule disjI2, intro exI[of _ "[]"] exI[of _ h] exI[of _ beta])
           (use a h source in simp)
    qed
  qed
next
  case (Fun f ts)
  show ?case
  proof -
    from Fun.prems(3) obtain i a' where a: "a = i # a'"
      and i: "i < length ts"
      and a_hole:
        "a' \<in> hole_poss
          (rhs_origin_mctxt_at l r p C (alpha @ [i]) (ts ! i))"
      by auto
    have alpha_i: "alpha @ [i] \<in> poss r"
      using Fun.prems(1) Fun.prems(2) i
      by (simp only: poss_append_poss) simp
    have at_i: "r |_ (alpha @ [i]) = ts ! i"
      using subt_at_append[OF Fun.prems(1), of "[i]"] Fun.prems(2) i by simp
    from Fun.hyps[OF nth_mem[OF i] alpha_i at_i a_hole]
    show ?thesis
    proof
      assume "\<exists>gamma beta.
        gamma \<in> var_poss (ts ! i) \<and> a' = gamma @ beta \<and>
        p @ rhs_predecessor l r ((alpha @ [i]) @ gamma) @ beta
          \<in> hole_poss C"
      then obtain gamma beta where gamma: "gamma \<in> var_poss (ts ! i)"
        and a': "a' = gamma @ beta"
        and source:
          "p @ rhs_predecessor l r ((alpha @ [i]) @ gamma) @ beta
            \<in> hole_poss C"
        by blast
      have lifted: "i # gamma \<in> var_poss (Fun f ts)" using i gamma by auto
      have a_lifted: "a = (i # gamma) @ beta" unfolding a a' by simp
      have source_lifted:
        "p @ rhs_predecessor l r (alpha @ (i # gamma)) @ beta
          \<in> hole_poss C"
        using source by (simp add: append_assoc)
      show ?thesis by (rule disjI1) (use lifted a_lifted source_lifted in blast)
    next
      assume "\<exists>gamma h beta.
        gamma \<in> var_poss (ts ! i) \<and> a' = gamma \<and>
        h \<in> hole_poss C \<and>
        p @ rhs_predecessor l r ((alpha @ [i]) @ gamma) = h @ beta"
      then obtain gamma h beta where gamma: "gamma \<in> var_poss (ts ! i)"
        and a': "a' = gamma" and h: "h \<in> hole_poss C"
        and source:
          "p @ rhs_predecessor l r ((alpha @ [i]) @ gamma) = h @ beta"
        by blast
      have lifted: "i # gamma \<in> var_poss (Fun f ts)" using i gamma by auto
      have a_lifted: "a = i # gamma" unfolding a a' by simp
      have source_lifted:
        "p @ rhs_predecessor l r (alpha @ (i # gamma)) = h @ beta"
        using source by (simp add: append_assoc)
      show ?thesis by (rule disjI2)
        (use lifted a_lifted h source_lifted in blast)
    qed
  qed
qed

lemma rhs_origin_mctxt_hole_root:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and C_prefix: "C \<le> mctxt_of_term s"
    and p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and hole: "a \<in> hole_poss (rhs_origin_mctxt l r p C)"
  shows
    "(\<exists>alpha beta.
       alpha \<in> var_poss r \<and> a = alpha @ beta \<and>
       p @ rhs_predecessor l r alpha @ beta \<in> hole_poss C) \<or>
     (\<exists>alpha h beta.
       alpha \<in> var_poss r \<and> a = alpha \<and>
       h \<in> hole_poss C \<and>
       p @ rhs_predecessor l r alpha = h @ beta)"
proof -
  have hole': "a \<in> hole_poss (rhs_origin_mctxt_at l r p C [] r)"
    using hole unfolding rhs_origin_mctxt_def .
  from rhs_origin_mctxt_hole[OF nd C_prefix p redex, of "[]" r a, OF _ _ hole']
  show ?thesis by simp
qed

end
