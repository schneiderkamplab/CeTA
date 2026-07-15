(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
License: LGPL (see file COPYING.LESSER)
*)
theory Trs_Impl_More
  imports 
    First_Order_Rewriting.Trs_Impl
    First_Order_Rewriting.Rewrite_Relations_Impl
    Renaming_Interpretations
begin

context
  fixes R :: "('f,'v)rules"
  assumes wf: "wf_trs (set R)" 
begin

(* TODO: move to AFP *)
lemma mstep_mstep_rewrite_main:
  assumes "(s, t) \<in> mstep (set R)"
  shows "t \<in> set (mstep_rewrite_main R s)"
proof -
  note simp[simp] = mstep_rewrite_main.simps[OF wf]
  show ?thesis using assms
  proof induction
    case (Var x)
    then show ?case by auto
  next
    case (args f n ss ts)
    show ?case unfolding simp set_remdups set_append set_map
    proof (intro UnI2 imageI)
      show "ts \<in> set (product_lists (map (mstep_rewrite_main R) ss))" 
        unfolding product_lists_set
        by (intro CollectI list_all2_all_nthI, insert args, auto)
    qed
  next
    case (rule l r \<sigma> \<tau>)
    from wf rule obtain f ls where l: "l = Fun f ls" by (cases l, auto simp: wf_trs_def)
    hence lsig: "l \<cdot> \<sigma> = Fun f (map (\<lambda> li. li \<cdot> \<sigma>) ls)" by auto
    from match_complete'[of l \<sigma>, OF refl] obtain \<sigma>'
      where match: "Matching.match (l \<cdot> \<sigma>) l = Some \<sigma>'" and sigma': "(\<forall>x\<in>vars_term l. \<sigma> x = \<sigma>' x)"
      by auto
    from wf rule have sub: "vars_term r \<subseteq> vars_term l" unfolding wf_trs_def by auto
    with sigma'
    have "map \<sigma> (vars_distinct r) = map \<sigma>' (vars_distinct r)"  
      by (intro map_cong, auto)
    hence mem: "(r, map \<sigma> (vars_distinct r)) \<in> set (root_subst_with_rhs R (l \<cdot> \<sigma>))" 
      using match unfolding root_subst_with_rhs.simps using \<open>(l,r) \<in> set R\<close> by force 
    show ?case unfolding lsig simp set_remdups set_append set_concat
      unfolding lsig[symmetric] set_map image_comp o_def[of set]
    proof (intro UnI1, rule UN_I[OF mem], unfold split set_map, intro rev_image_eqI)
      let ?vs = "vars_distinct r" 
      define vs where "vs = ?vs" 
      have dist: "distinct vs" unfolding vs_def by auto
      show "r \<cdot> \<tau> = r \<cdot> mk_subst Var (zip ?vs (map \<tau> ?vs))"
      proof (intro term_subst_eq, unfold vs_def[symmetric])
        fix x
        assume "x \<in> vars_term r" 
        hence "x \<in> set vs" by (auto simp: vs_def)
        then obtain i where i: "i < length vs" and x: "x = vs ! i" by (auto simp: set_conv_nth)
        show "\<tau> x = mk_subst Var (zip vs (map \<tau> vs)) x" 
          unfolding x 
          by (subst mk_subst_distinct[OF dist i], insert i, auto)
      qed
      show "map \<tau> (vars_distinct r) \<in> set (product_lists (map (mstep_rewrite_main R) (map \<sigma> (vars_distinct r))))" 
        unfolding product_lists_set vs_def[symmetric] map_map unfolding o_def
        by (intro CollectI list_all2_map_map, insert rule sub, auto simp: vs_def)
    qed
  qed
qed

lemma set_mstep_rewrite_main: "set (mstep_rewrite_main R s) = { t. (s, t) \<in> mstep (set R)}"
  using mstep_mstep_rewrite_main mstep_rewrite_main_mstep[OF wf] by blast

end


abbreviation "terms_of_rules rs \<equiv> map fst rs @ map snd rs"
  
definition "match_rules rs\<^sub>1 rs\<^sub>2 = do {
  ts \<leftarrow> zip_option (terms_of_rules rs\<^sub>2) (terms_of_rules rs\<^sub>1);
  match_list Var ts
}"

abbreviation "term_of_rules rs \<equiv> Fun undefined (terms_of_rules rs)"

lemma match_rules_alt_def:
  "match_rules rs\<^sub>1 rs\<^sub>2 = match (term_of_rules rs\<^sub>1) (term_of_rules rs\<^sub>2)"
  by (cases "zip_option (terms_of_rules rs\<^sub>1) (terms_of_rules rs\<^sub>2)")
    (auto simp: match_rules_def match_def match_list_def decompose_def
          split: option.splits Option.bind_splits)

lemma rules_enc_aux:
  fixes xs ys :: "('f, 'v :: infinite) rules"
  assumes "map ((\<bullet>) \<pi> \<circ> fst) xs @ map ((\<bullet>) \<pi> \<circ> snd) xs = map fst ys @ map snd ys"
  shows "map ((\<bullet>) \<pi>) xs = ys"
proof -
  have "length xs = length ys"
  proof (rule ccontr)
    assume "length xs \<noteq> length ys"
    moreover
    have "length (map ((\<bullet>) \<pi> \<circ> fst) xs @ map ((\<bullet>) \<pi> \<circ> snd) xs) = length (map fst ys @ map snd ys)"
      using assms by simp
    ultimately show False by simp
  qed
  then show ?thesis
    using assms by (induct xs ys rule: list_induct2; auto simp: eqvt)
qed

lemma perm_term_of_rules_eq_conv:
  "\<pi> \<bullet> term_of_rules rs\<^sub>1 = term_of_rules rs\<^sub>2 \<longleftrightarrow> \<pi> \<bullet> rs\<^sub>1 = rs\<^sub>2"
  by (auto simp: eqvt rules_enc_aux)

lemma match_rules_imp_variants:
  fixes rs\<^sub>1 rs\<^sub>2 :: "('f, 'v :: infinite) rules"
  assumes "match_rules rs\<^sub>2 rs\<^sub>1 = Some \<sigma>\<^sub>1" and "match_rules rs\<^sub>1 rs\<^sub>2 = Some \<sigma>\<^sub>2"
  shows "\<exists>\<pi>::'v perm. \<pi> \<bullet> rs\<^sub>1 = rs\<^sub>2"
proof -
  have "term_of_rules rs\<^sub>2 \<cdot> \<sigma>\<^sub>2 = term_of_rules rs\<^sub>1"
    and "term_of_rules rs\<^sub>1 \<cdot> \<sigma>\<^sub>1 = term_of_rules rs\<^sub>2"
    using assms by (auto simp: match_rules_alt_def dest: match_sound)
  then obtain \<pi> :: "'v perm" where "\<pi> \<bullet> rs\<^sub>2 = rs\<^sub>1"
    using term_variants_iff [of "term_of_rules rs\<^sub>2" "term_of_rules rs\<^sub>1"]
    unfolding perm_term_of_rules_eq_conv by auto
  then have "-\<pi> \<bullet> rs\<^sub>1 = rs\<^sub>2" by (auto simp del: rules_pt.permute_list_def)
  then show ?thesis ..
qed

definition
  "check_variants_rule r r' = do {
    check (match_rules [r] [r'] \<noteq> None \<and> match_rules [r'] [r] \<noteq> None)
      (showsl_rule r \<circ> showsl (STR '' and '') \<circ> showsl_rule r' \<circ> showsl (STR '' are not variants of each other\<newline>''))
  }"

lemma check_variants_rule [elim!]:
  assumes "isOK (check_variants_rule r r')"
  obtains p where "p \<bullet> r = r'"
  using assms
  by (cases r; cases r') (auto simp: check_variants_rule_def eqvt dest: match_rules_imp_variants)

definition
  "check_variant_in_trs R r =
    check_exm (check_variants_rule r) R (showsl_sep id id)
    <+? (\<lambda>_. showsl_rule r \<circ> showsl (STR '' is not a variant of any rule in '') \<circ> showsl_trs R)"

lemma check_variant_in_trs [elim!]:
  assumes "isOK (check_variant_in_trs R r)"
  obtains p where "p \<bullet> r \<in> set R"
  using assms by (cases r) (force simp: check_variant_in_trs_def eqvt)

definition "check_variants_trs R R' = check_allm (check_variant_in_trs R') R"

lemma check_variants_trs [dest!]:
  assumes "isOK (check_variants_trs R R')"
  shows "\<forall>r \<in> set R. \<exists>p. p \<bullet> r \<in> set R'"
  using assms by (auto simp: check_variants_trs_def)

lemma check_variants_trs_rstep: assumes "isOK(check_variants_trs 
  (R :: ('f :: showl,'v :: {infinite,showl})rules) S)"
  shows "rstep (set R) \<subseteq> rstep (set S)" 
  using check_variants_trs[OF assms]
    by (metis (no_types, opaque_lifting) perm_rstep_conv rstep_mono rstep_simps(2) subset_code(1) subset_rstep)

end