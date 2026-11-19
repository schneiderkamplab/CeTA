theory LP_Cut_Extended_MGU
  imports Category_LP_Cut_Arity_MGU_Bridge.LP_MGU_Concrete_Extension
begin

lemma cut_rank_unrank_atom_arguments:
  assumes "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments a)"
  shows "logic_atom_map cut_rank_tree (logic_atom_map cut_unrank_tree a) = a"
  using assms by (cases a)
    (auto simp: map_map o_def list_all_iff intro!: map_idI intro: cut_rank_unrank_tree)

lemma cut_unrank_extended_mgu:
  assumes mgu: "logic_mgu E a b s"
    and left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments b)"
    and correct: "\<And>x. logic_tree_arity_correct (logic_symbol_arity snd) (s x)"
    and encode: "\<And>t. D t \<Longrightarrow> E (cut_rank_tree t)"
    and decode: "\<And>t. E t \<Longrightarrow> D (cut_unrank_tree t)"
  shows "logic_mgu D (logic_atom_map cut_unrank_tree a) (logic_atom_map cut_unrank_tree b)
    (cut_unrank_tree \<circ> s)"
proof -
  have ss: "cut_rank_tree \<circ> (cut_unrank_tree \<circ> s) = s"
    by (rule ext) (simp add: cut_rank_unrank_tree[OF correct])
  have encoded: "logic_mgu E
      (logic_atom_map cut_rank_tree (logic_atom_map cut_unrank_tree a))
      (logic_atom_map cut_rank_tree (logic_atom_map cut_unrank_tree b))
      (cut_rank_tree \<circ> (cut_unrank_tree \<circ> s))"
    using mgu by (simp only: ss cut_rank_unrank_atom_arguments[OF left]
      cut_rank_unrank_atom_arguments[OF right])
  show ?thesis by (rule logic_mgu_encoding_reflect[where F=cut_rank_tree and G=cut_unrank_tree and D=D and E=E,
    OF cut_unrank_rank_tree cut_rank_subst cut_unrank_subst encode decode encoded])
qed

lemma cut_unrank_finite_mgu:
  fixes s :: "string \<Rightarrow> (('f \<times> nat) logic_symbol,string) logic_tree"
  assumes mgu: "logic_mgu (\<lambda>t. logic_finite t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t) a b s"
    and left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments b)"
  shows "logic_mgu logic_finite (logic_atom_map cut_unrank_tree a) (logic_atom_map cut_unrank_tree b)
    (cut_unrank_tree \<circ> s)"
proof -
  have correct: "logic_tree_arity_correct (logic_symbol_arity snd) (s x)" for x
    using mgu by (auto simp: logic_mgu_def logic_substitution_in_def)
  have extended: "logic_mgu logic_finite a b s"
    by (rule logic_finite_mgu_arity_extension[OF mgu left right])
  show ?thesis by (rule cut_unrank_extended_mgu[OF extended left right correct])
    (auto simp: cut_rank_finite intro: cut_unrank_finite)
qed

lemma cut_unrank_rational_mgu:
  fixes s :: "string \<Rightarrow> (('f \<times> nat) logic_symbol,string) logic_tree"
  assumes mgu: "logic_mgu (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t) a b s"
    and left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments b)"
  shows "logic_mgu logic_rational (logic_atom_map cut_unrank_tree a) (logic_atom_map cut_unrank_tree b)
    (cut_unrank_tree \<circ> s)"
proof -
  have correct: "logic_tree_arity_correct (logic_symbol_arity snd) (s x)" for x
    using mgu by (auto simp: logic_mgu_def logic_substitution_in_def)
  have extended: "logic_mgu logic_rational a b s"
    by (rule logic_rational_mgu_arity_extension[OF mgu left right])
  show ?thesis by (rule cut_unrank_extended_mgu[OF extended left right correct])
    (auto simp: cut_rank_rational intro: cut_unrank_rational)
qed

lemma cut_unrank_infinite_mgu:
  fixes s :: "string \<Rightarrow> (('f \<times> nat) logic_symbol,string) logic_tree"
  assumes mgu: "logic_mgu (logic_tree_arity_correct (logic_symbol_arity snd)) a b s"
    and left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments b)"
  shows "logic_mgu (\<lambda>_. True) (logic_atom_map cut_unrank_tree a) (logic_atom_map cut_unrank_tree b)
    (cut_unrank_tree \<circ> s)"
proof -
  have correct: "logic_tree_arity_correct (logic_symbol_arity snd) (s x)" for x
    using mgu by (auto simp: logic_mgu_def logic_substitution_in_def)
  have extended: "logic_mgu (\<lambda>_. True) a b s"
    by (rule logic_infinite_mgu_arity_extension[OF mgu left right])
  show ?thesis by (rule cut_unrank_extended_mgu[OF extended left right correct])
    simp_all
qed

lemma logic_mgu_cut_atom:
  "logic_mgu D (LAtom p ts) (LAtom q us) s =
    logic_mgu D (LAtom () [LFun (LogicUser p) ts]) (LAtom () [LFun (LogicUser q) us]) s"
  by (simp add: logic_mgu_def)

ML \<open>
  val results = @{thms cut_unrank_finite_mgu cut_unrank_rational_mgu cut_unrank_infinite_mgu logic_mgu_cut_atom}
  val _ = if Thm_Deps.has_skip_proof results then error "Extended cut MGU: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Extended cut MGU: oracle dependency"
\<close>
end
