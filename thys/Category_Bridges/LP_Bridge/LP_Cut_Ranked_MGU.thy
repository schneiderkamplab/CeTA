theory LP_Cut_Ranked_MGU
  imports Category_LP_Bridge.LP_Cut_Ranked_Representation
    Category_Properties.LP_Arity_MGU_Properties
begin

text \<open>A substitution-preserving encoding transports global MGUs to its
image. The target domain need only be a retraction image, not the entire target
type. This separates name ranking from the restriction to correct control arities.\<close>
lemma logic_mgu_encoding:
  fixes F :: "('f,'v) logic_tree \<Rightarrow> ('g,'v) logic_tree"
    and G :: "('g,'v) logic_tree \<Rightarrow> ('f,'v) logic_tree"
  assumes inverse: "\<And>t. G (F t) = t"
    and forward_subst: "\<And>s t. F (logic_subst s t) = logic_subst (F \<circ> s) (F t)"
    and backward_subst: "\<And>s t. G (logic_subst s t) = logic_subst (G \<circ> s) (G t)"
    and encode_domain: "\<And>t. D t \<Longrightarrow> E (F t)"
    and decode_domain: "\<And>t. E t \<Longrightarrow> D (G t)"
    and image: "\<And>t. E t \<Longrightarrow> F (G t) = t"
    and mgu: "logic_mgu D a b s"
  shows "logic_mgu E (logic_atom_map F a) (logic_atom_map F b) (F \<circ> s)"
proof -
  have domain: "logic_substitution_in E (F \<circ> s)"
    using mgu encode_domain by (auto simp: logic_mgu_def logic_substitution_in_def)
  have equation: "logic_atom_map (logic_subst (F \<circ> s)) (logic_atom_map F a) =
      logic_atom_map (logic_subst (F \<circ> s)) (logic_atom_map F b)"
    using arg_cong[where f="logic_atom_map F",
      OF conjunct1[OF conjunct2[OF mgu[unfolded logic_mgu_def]]]]
    by (cases a; cases b) (simp add: map_map o_def forward_subst)
  have factors: "\<exists>v. logic_substitution_in E v \<and>
      (\<forall>x. u x = logic_subst v ((F \<circ> s) x))"
    if ud: "logic_substitution_in E u"
      and ue: "logic_atom_map (logic_subst u) (logic_atom_map F a) =
        logic_atom_map (logic_subst u) (logic_atom_map F b)" for u
  proof -
    have raw_domain: "logic_substitution_in D (G \<circ> u)"
      using ud decode_domain by (auto simp: logic_substitution_in_def)
    have raw_equation: "logic_atom_map (logic_subst (G \<circ> u)) a =
        logic_atom_map (logic_subst (G \<circ> u)) b"
      using arg_cong[OF ue, where f="logic_atom_map G"]
      by (cases a; cases b) (simp add: map_map o_def backward_subst inverse)
    obtain v where vd: "logic_substitution_in D v"
      and factor: "\<And>x. G (u x) = logic_subst v (s x)"
      using mgu raw_domain raw_equation unfolding logic_mgu_def by auto
    have encoded: "u x = logic_subst (F \<circ> v) (F (s x))" for x
      using arg_cong[OF factor[of x], where f=F] ud image
      by (simp add: logic_substitution_in_def forward_subst)
    show ?thesis by (intro exI[of _ "F \<circ> v"])
      (use vd encode_domain encoded in \<open>auto simp: logic_substitution_in_def\<close>)
  qed
  show ?thesis using domain equation factors unfolding logic_mgu_def by blast
qed

lemma cut_rank_image_mgu:
  assumes "logic_mgu D a b s"
  shows "logic_mgu (\<lambda>t. D (cut_unrank_tree t) \<and> cut_rank_tree (cut_unrank_tree t) = t)
    (logic_atom_map cut_rank_tree a) (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> s)"
  by (rule logic_mgu_encoding[where G=cut_unrank_tree, OF _ cut_rank_subst cut_unrank_subst _ _ _ assms]) simp_all

lemma cut_rank_typed_mgu:
  assumes mgu: "logic_mgu D a b s"
    and left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree a))"
    and right: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree b))"
    and closed: "\<And>t. D (cut_unrank_tree t) \<Longrightarrow> cut_rank_tree (cut_unrank_tree t) = t \<Longrightarrow>
      D (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z t))"
  shows "logic_mgu (\<lambda>t. D (cut_unrank_tree t) \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)
    (logic_atom_map cut_rank_tree a) (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> s)"
proof -
  let ?E = "\<lambda>t. D (cut_unrank_tree t) \<and> cut_rank_tree (cut_unrank_tree t) = t"
  have closure: "?E t \<Longrightarrow> ?E (logic_arity_project (logic_symbol_arity snd) z t)" for t
    using closed by (auto intro: cut_rank_unrank_tree logic_arity_project_correct)
  have typed: "logic_mgu (\<lambda>t. ?E t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)
      (logic_atom_map cut_rank_tree a) (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> s)"
    by (rule logic_mgu_correct_arity[OF cut_rank_image_mgu[OF mgu] left right closure])
  have domains: "(\<lambda>t. ?E t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t) =
      (\<lambda>t. D (cut_unrank_tree t) \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto intro: cut_rank_unrank_tree)
  show ?thesis using typed unfolding domains .
qed

lemma cut_unrank_finite:
  "logic_finite t \<Longrightarrow> logic_finite (cut_unrank_tree t)"
  by (auto simp: logic_finite_def cut_unrank_embed)
lemma cut_typed_unrank_finite:
  "logic_tree_arity_correct (logic_symbol_arity snd) t \<Longrightarrow>
    logic_finite (cut_unrank_tree t) = logic_finite t"
  by (metis cut_rank_finite cut_rank_unrank_tree)
lemma cut_typed_unrank_rational:
  "logic_tree_arity_correct (logic_symbol_arity snd) t \<Longrightarrow>
    logic_rational (cut_unrank_tree t) = logic_rational t"
  by (metis cut_rank_rational cut_rank_unrank_tree)
lemma cut_finite_projection_closed:
  "logic_finite (cut_unrank_tree t) \<Longrightarrow> cut_rank_tree (cut_unrank_tree t) = t \<Longrightarrow>
    logic_finite (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z t))"
  by (metis cut_rank_finite logic_arity_project_finite cut_unrank_finite)
lemma cut_rational_projection_closed:
  "logic_rational (cut_unrank_tree t) \<Longrightarrow> cut_rank_tree (cut_unrank_tree t) = t \<Longrightarrow>
    logic_rational (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z t))"
  by (metis cut_rank_rational logic_arity_project_rational cut_unrank_rational)


lemma cut_rank_finite_mgu:
  assumes mgu: "logic_mgu logic_finite a b s"
    and left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree a))"
    and right: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree b))"
  shows "logic_mgu (\<lambda>t. logic_finite t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)
    (logic_atom_map cut_rank_tree a) (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> s)"
proof -
  have domains: "(\<lambda>t. logic_finite (cut_unrank_tree t) \<and> logic_tree_arity_correct (logic_symbol_arity snd) t) =
      (\<lambda>t. logic_finite t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto simp: cut_typed_unrank_finite)
  show ?thesis using cut_rank_typed_mgu[OF mgu left right cut_finite_projection_closed]
    unfolding domains .
qed
lemma cut_rank_rational_mgu:
  assumes mgu: "logic_mgu logic_rational a b s"
    and left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree a))"
    and right: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree b))"
  shows "logic_mgu (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)
    (logic_atom_map cut_rank_tree a) (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> s)"
proof -
  have domains: "(\<lambda>t. logic_rational (cut_unrank_tree t) \<and> logic_tree_arity_correct (logic_symbol_arity snd) t) =
      (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto simp: cut_typed_unrank_rational)
  show ?thesis using cut_rank_typed_mgu[OF mgu left right cut_rational_projection_closed]
    unfolding domains .
qed
lemma cut_rank_infinite_mgu:
  assumes mgu: "logic_mgu (\<lambda>_. True) a b s"
    and left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree a))"
    and right: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree b))"
  shows "logic_mgu (logic_tree_arity_correct (logic_symbol_arity snd))
    (logic_atom_map cut_rank_tree a) (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> s)"
  using cut_rank_typed_mgu[OF mgu left right] by simp

definition cut_rank_runtime_atom :: "('f,('f logic_symbol,'v) logic_tree) logic_atom \<Rightarrow>
    ('f \<times> nat,(('f \<times> nat) logic_symbol,'v) logic_tree) logic_atom" where
  "cut_rank_runtime_atom a = logic_tag_atom (logic_atom_map cut_rank_tree a)"
lemma cut_rank_runtime_atom_embed:
  "cut_rank_runtime_atom (logic_atom_map logic_embed a) = logic_atom_map logic_embed (cut_rank_atom a)"
  by (cases a) (simp add: cut_rank_runtime_atom_def map_map o_def cut_rank_embed)
lemma cut_rank_runtime_atom_subst:
  "cut_rank_runtime_atom (logic_atom_map (logic_subst s) a) =
    logic_atom_map (logic_subst (cut_rank_tree \<circ> s)) (cut_rank_runtime_atom a)"
  by (cases a) (simp add: cut_rank_runtime_atom_def map_map o_def cut_rank_subst)
lemma cut_rank_runtime_atom_mgu:
  "logic_mgu E (cut_rank_runtime_atom a) (cut_rank_runtime_atom b) s =
    logic_mgu E (logic_atom_map cut_rank_tree a) (logic_atom_map cut_rank_tree b) s"
  by (simp add: cut_rank_runtime_atom_def logic_tag_mgu)

ML \<open>
  val results = @{thms logic_mgu_encoding cut_rank_finite_mgu cut_rank_rational_mgu cut_rank_infinite_mgu}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut ranked MGU: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = if null names then () else error ("Cut ranked MGU: oracle dependencies: " ^ commas names)
\<close>
end
