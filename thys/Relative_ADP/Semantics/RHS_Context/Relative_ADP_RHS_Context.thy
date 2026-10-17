theory Relative_ADP_RHS_Context
  imports Relative_ADP_Outer_State_Dev.Relative_ADP_Outer_State
begin

fun rhs_origin_mctxt_at ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow>
    ('f, 'v) mctxt \<Rightarrow> pos \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) mctxt" where
  "rhs_origin_mctxt_at l r p C alpha (Var x) =
    (let rho = rhs_predecessor l r alpha in
      if p @ rho \<in> poss_mctxt C then subm_at C (p @ rho) else MHole)"
| "rhs_origin_mctxt_at l r p C alpha (Fun f ts) =
    MFun f (map (\<lambda>i. rhs_origin_mctxt_at l r p C (alpha @ [i]) (ts ! i))
      [0..<length ts])"

definition rhs_origin_mctxt ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow>
    ('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt" where
  "rhs_origin_mctxt l r p C = rhs_origin_mctxt_at l r p C [] r"

lemma poss_mctxt_subm_at_append:
  assumes source: "a \<in> poss_mctxt C"
    and below: "b \<in> poss_mctxt (subm_at C a)"
  shows "a @ b \<in> poss_mctxt C"
  using poss_mctxt_append_poss_mctxt[of a b C] source below
  by (auto simp: all_poss_mctxt_conv)

lemma rhs_origin_mctxt_position:
  assumes q: "q \<in> poss_mctxt (rhs_origin_mctxt_at l r p C alpha t)"
  shows
    "q \<in> fun_poss t \<or>
     (\<exists>gamma beta.
       gamma \<in> var_poss t \<and>
       q = gamma @ beta \<and>
       p @ rhs_predecessor l r (alpha @ gamma) @ beta \<in> poss_mctxt C)"
  using q
proof (induct t arbitrary: alpha q)
  case (Var x)
  let ?rho = "rhs_predecessor l r alpha"
  from Var.prems have restored:
    "p @ ?rho \<in> poss_mctxt C" and
    q_sub: "q \<in> poss_mctxt (subm_at C (p @ ?rho))"
    by (auto simp: Let_def split: if_splits)
  have source: "p @ ?rho @ q \<in> poss_mctxt C"
    using poss_mctxt_subm_at_append[OF restored q_sub]
    by (simp add: append_assoc)
  show ?case
    by (rule disjI2, intro exI[of _ "[]"] exI[of _ q])
       (use source in simp)
next
  case (Fun f ts)
  show ?case
  proof (cases q)
    case Nil
    then show ?thesis by simp
  next
    case (Cons i q')
    from Fun.prems[unfolded Cons]
    have i: "i < length ts"
      and q': "q' \<in> poss_mctxt
        (rhs_origin_mctxt_at l r p C (alpha @ [i]) (ts ! i))"
      by auto
    note IH = Fun.hyps[OF nth_mem[OF i]]
    have classified:
      "q' \<in> fun_poss (ts ! i) \<or>
       (\<exists>gamma beta.
         gamma \<in> var_poss (ts ! i) \<and>
         q' = gamma @ beta \<and>
         p @ rhs_predecessor l r (alpha @ [i] @ gamma) @ beta
           \<in> poss_mctxt C)"
      using IH[of q' "alpha @ [i]"] q' by simp
    then show ?thesis
    proof
      assume "q' \<in> fun_poss (ts ! i)"
      then show ?thesis using i unfolding Cons by auto
    next
      assume "\<exists>gamma beta.
         gamma \<in> var_poss (ts ! i) \<and>
         q' = gamma @ beta \<and>
         p @ rhs_predecessor l r (alpha @ [i] @ gamma) @ beta
           \<in> poss_mctxt C"
      then obtain gamma beta where
        gamma: "gamma \<in> var_poss (ts ! i)" and q': "q' = gamma @ beta"
        and source:
          "p @ rhs_predecessor l r (alpha @ [i] @ gamma) @ beta
            \<in> poss_mctxt C" by blast
      have "i # gamma \<in> var_poss (Fun f ts)"
        using i gamma by auto
      moreover have "q = (i # gamma) @ beta" unfolding Cons q' by simp
      moreover have
        "p @ rhs_predecessor l r (alpha @ (i # gamma)) @ beta
          \<in> poss_mctxt C"
        using source by (simp add: append_assoc)
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma rhs_origin_mctxt_position_root:
  assumes q: "q \<in> poss_mctxt (rhs_origin_mctxt l r p C)"
  shows
    "q \<in> fun_poss r \<or>
     (\<exists>alpha beta.
       alpha \<in> var_poss r \<and> q = alpha @ beta \<and>
       p @ rhs_predecessor l r alpha @ beta \<in> poss_mctxt C)"
proof -
  have q': "q \<in> poss_mctxt (rhs_origin_mctxt_at l r p C [] r)"
    using q unfolding rhs_origin_mctxt_def .
  show ?thesis
    using rhs_origin_mctxt_position[OF q'] by simp
qed

end
