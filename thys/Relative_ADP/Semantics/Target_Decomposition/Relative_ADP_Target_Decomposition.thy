theory Relative_ADP_Target_Decomposition
  imports Relative_ADP_Concrete_Transfer_Dev.Relative_ADP_Concrete_Transfer
begin

lemma mctxt_of_term_replace_at:
  assumes p: "p \<in> poss s"
  shows "mctxt_of_term (replace_at s p t) =
    mreplace_at (mctxt_of_term s) p (mctxt_of_term t)"
  using p
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ss where s: "s = Fun f ss"
    and i: "i < length ss" and p: "p \<in> poss (ss ! i)"
    by (cases s) auto
  show ?case unfolding s
    using Cons.hyps[OF p] i
    by (simp add: upd_conv_take_nth_drop map_update take_map drop_map)
qed

lemma rhs_origin_mctxt_at_prefix:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and C_prefix: "C \<le> mctxt_of_term s"
    and p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and alpha: "alpha \<in> poss r"
    and at: "r |_ alpha = t"
  shows "rhs_origin_mctxt_at l r p C alpha t \<le> mctxt_of_term (t \<cdot> sigma)"
  using alpha at
proof (induct t arbitrary: alpha)
  case (Var x)
  have alpha_var: "alpha \<in> var_poss r"
    unfolding var_poss_iff using Var.prems by blast
  let ?rho = "rhs_predecessor l r alpha"
  have rho: "?rho \<in> var_poss l"
    by (rule rhs_predecessor_properties(1)[OF nd alpha_var])
  have rho_at: "l |_ ?rho = Var x"
    using rhs_predecessor_properties(2)[OF nd alpha_var] Var.prems(2) by simp
  show ?case
  proof (cases "p @ ?rho \<in> poss_mctxt C")
    case False
    then show ?thesis by (simp add: Let_def)
  next
    case True
    have source_all: "p @ ?rho \<in> all_poss_mctxt C"
      using True unfolding all_poss_mctxt_conv by blast
    have source_term: "p @ ?rho \<in> poss s"
    proof -
      have "p @ ?rho \<in> all_poss_mctxt (mctxt_of_term s)"
        by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] source_all])
      then show ?thesis by simp
    qed
    have source_prefix:
      "subm_at C (p @ ?rho) \<le>
        subm_at (mctxt_of_term s) (p @ ?rho)"
      by (rule less_eq_subm_at[OF source_all C_prefix])
    have source_at: "s |_ (p @ ?rho) = sigma x"
    proof -
      have rho_poss: "?rho \<in> poss l"
        by (rule var_poss_imp_poss[OF rho])
      have p_rho: "p @ ?rho \<in> poss s"
        using p rho_poss redex by (simp only: poss_append_poss) simp
      have split: "s |_ (p @ ?rho) = (s |_ p) |_ ?rho"
        by (rule subt_at_append[OF p])
      have subst_at: "(l \<cdot> sigma) |_ ?rho = sigma x"
        using subt_at_subst[OF rho_poss, of sigma] rho_at by simp
      show ?thesis using split redex subst_at by simp
    qed
    have target:
      "subm_at (mctxt_of_term s) (p @ ?rho) = mctxt_of_term (sigma x)"
      using subm_at_mctxt_of_term[OF source_term] source_at by simp
    show ?thesis using source_prefix target True by (simp add: Let_def)
  qed
next
  case (Fun f ts)
  from Fun.prems obtain r_at: "r |_ alpha = Fun f ts" by simp
  have child:
    "rhs_origin_mctxt_at l r p C (alpha @ [i]) (ts ! i)
      \<le> mctxt_of_term (ts ! i \<cdot> sigma)"
    if i: "i < length ts" for i
  proof -
    have alpha_i: "alpha @ [i] \<in> poss r"
      using Fun.prems(1) i r_at by (simp only: poss_append_poss) simp
    have at_i: "r |_ (alpha @ [i]) = ts ! i"
      using subt_at_append[OF Fun.prems(1), of "[i]"] r_at i by simp
    show ?thesis
      by (rule Fun.hyps[OF nth_mem[OF i] alpha_i at_i])
  qed
  show ?case
    using child by (auto simp: less_eq_mctxt_def map_nth_eq_conv)
qed

lemma rhs_origin_mctxt_prefix:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and C_prefix: "C \<le> mctxt_of_term s"
    and p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
  shows "rhs_origin_mctxt l r p C \<le> mctxt_of_term (r \<cdot> sigma)"
  unfolding rhs_origin_mctxt_def
  by (rule rhs_origin_mctxt_at_prefix[OF nd C_prefix p redex]) simp_all

lemma concrete_target_context_prefix:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and length: "num_holes C = length holes"
    and source: "fill_holes C holes = s"
    and p_context: "p \<in> poss_mctxt C"
    and redex: "s |_ p = l \<cdot> sigma"
  shows "mreplace_at C p (rhs_origin_mctxt l r p C) \<le>
    mctxt_of_term (replace_at s p (r \<cdot> sigma))"
proof -
  have C_prefix: "C \<le> mctxt_of_term s"
    using fill_holes_suffix[OF length] source by simp
  have p_all: "p \<in> all_poss_mctxt C"
    using p_context unfolding all_poss_mctxt_conv by blast
  have p: "p \<in> poss s"
  proof -
    have "p \<in> all_poss_mctxt (mctxt_of_term s)"
      by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] p_all])
    then show ?thesis by simp
  qed
  have rhs_prefix:
    "rhs_origin_mctxt l r p C \<le> mctxt_of_term (r \<cdot> sigma)"
    by (rule rhs_origin_mctxt_prefix[OF nd C_prefix p redex])
  have replacement_prefix:
    "mreplace_at C p (rhs_origin_mctxt l r p C) \<le>
      mreplace_at (mctxt_of_term s) p (mctxt_of_term (r \<cdot> sigma))"
    by (rule compare_mreplace_atI[OF C_prefix rhs_prefix p_context])
  show ?thesis
    using replacement_prefix mctxt_of_term_replace_at[OF p, of "r \<cdot> sigma"]
    by simp
qed

lemma concrete_target_decomposition:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and length: "num_holes C = length holes"
    and source: "fill_holes C holes = s"
    and p_context: "p \<in> poss_mctxt C"
    and redex: "s |_ p = l \<cdot> sigma"
  defines "C' \<equiv> mreplace_at C p (rhs_origin_mctxt l r p C)"
    and "t \<equiv> replace_at s p (r \<cdot> sigma)"
  shows "num_holes C' = length (unfill_holes C' t)"
    and "fill_holes C' (unfill_holes C' t) = t"
proof -
  have prefix: "C' \<le> mctxt_of_term t"
    unfolding C'_def t_def
    by (rule concrete_target_context_prefix[OF nd length source p_context redex])
  show "num_holes C' = length (unfill_holes C' t)"
    using length_unfill_holes[OF prefix] by simp
  show "fill_holes C' (unfill_holes C' t) = t"
    by (rule fill_unfill_holes[OF prefix])
qed

end
