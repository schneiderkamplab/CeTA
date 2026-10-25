theory LP_Dependency_Triples
  imports LP_SEG_Answers
begin

text \<open>Dependency triples retain the successful prefix separately from
the selected recursive call. Extraction completeness alone is not a source
termination theorem; the SEG and Pi-DP connections are separate obligations.\<close>

type_synonym ('f,'v) lp_dependency_triple =
  "('f,'v) lp_atom \<times> ('f,'v) lp_atom list \<times> ('f,'v) lp_atom"

definition lp_clause_triples ::
  "('f,'v) lp_clause \<Rightarrow> ('f,'v) lp_dependency_triple list" where
  "lp_clause_triples c = map (\<lambda>i. (fst c, take i (snd c), snd c ! i))
    [0..<length (snd c)]"

definition lp_dependency_triples where
  "lp_dependency_triples P = concat (map lp_clause_triples P)"

lemma lp_clause_triples_exact:
  "(h, ps, b) \<in> set (lp_clause_triples c) \<longleftrightarrow>
    (\<exists>i<length (snd c). h=fst c \<and> ps=take i (snd c) \<and> b=snd c!i)"
  by (auto simp: lp_clause_triples_def)

lemma lp_dependency_triples_exact:
  "(h, ps, b) \<in> set (lp_dependency_triples P) \<longleftrightarrow>
    (\<exists>c\<in>set P. \<exists>i<length (snd c).
      h=fst c \<and> ps=take i (snd c) \<and> b=snd c!i)"
  by (auto simp: lp_dependency_triples_def lp_clause_triples_exact)

lemma lp_dependency_triple_source_suffix:
  assumes "(h, ps, b) \<in> set (lp_dependency_triples P)"
  shows "\<exists>rest. (h, ps @ b # rest) \<in> set P"
proof -
  obtain c i where c: "c\<in>set P" and i: "i<length (snd c)"
    and shape: "h=fst c" "ps=take i (snd c)" "b=snd c!i"
    using assms by (auto simp: lp_dependency_triples_exact)
  have body: "snd c = take i (snd c) @ snd c!i # drop (Suc i) (snd c)"
    using i by (simp add: id_take_nth_drop)
  show ?thesis using c body shape by (intro exI[of _ "drop (Suc i) (snd c)"]) auto
qed

text \<open>A triple's prefix is a successful source computation, not merely
  a terminating one. Its answer environment is shared by the selected call
  and the remaining goals. This operational connection also permits infinite
  runtime terms, as does the underlying source semantics.\<close>

lemma lp_dependency_triple_source_execution:
  assumes triple: "(h, ps, b) \<in> set (lp_dependency_triples P)"
    and matching: "lp_iatom_subst a \<sigma> = lp_atom_eval h \<rho>"
    and success: "((map (\<lambda>g. lp_atom_eval g \<rho>) ps,\<rho>),([],\<eta>))
      \<in> (lp_seg_answer_step P)\<^sup>*"
  shows "\<exists>rest. (h, ps @ b # rest) \<in> set P \<and>
    ([a], lp_atom_eval b \<eta> # map (\<lambda>g. lp_atom_eval g \<eta>) rest)
      \<in> (lp_ild P)\<^sup>+"
proof -
  obtain rest where clause: "(h, ps @ b # rest) \<in> set P"
    using lp_dependency_triple_source_suffix[OF triple] by blast
  obtain c where c: "c < length P" and pc: "P!c = (h, ps @ b # rest)"
    using clause by (metis in_set_conv_nth)
  have match: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<rho>"
    using matching by (simp add: pc)
  have enter: "([a], map (\<lambda>g. lp_atom_eval g \<rho>) ps @
      map (\<lambda>g. lp_atom_eval g \<rho>) (b # rest)) \<in> lp_ild P"
    using lp_ild.resolve[OF c match, of "[]"] by (simp add: pc)
  have prefix_path: "(map (\<lambda>g. lp_atom_eval g \<rho>) ps @
      map (\<lambda>g. lp_atom_eval g \<rho>) (b # rest),
      map (\<lambda>g. lp_atom_eval g \<eta>) (b # rest)) \<in> (lp_ild P)\<^sup>*"
    using lp_seg_answer_steps_append[OF success, of "b # rest"] by simp
  have path: "([a], map (\<lambda>g. lp_atom_eval g \<eta>) (b # rest))
      \<in> (lp_ild P)\<^sup>+"
    using enter prefix_path by (meson r_into_trancl trancl_rtrancl_trancl)
  show ?thesis using clause path by auto
qed

end
