theory LP_MGU_Domain_Extension
  imports Category_LP_Cut_Ranked_Bridge.LP_Cut_Ranked_Table_Checker
begin

text \<open>A restricted MGU is also unrestricted when an unrestricted MGU
exists in the smaller domain. This is a factorization argument, not an
assumption that restricting signatures preserves termination. Existence must
be supplied separately wherever the lemma is used.\<close>
lemma logic_mgu_domain_extension:
  assumes small: "logic_mgu E a b s"
    and large: "logic_mgu D a b r"
    and rd: "logic_substitution_in E r"
    and inclusion: "\<And>t. E t \<Longrightarrow> D t"
    and closed: "\<And>v t. logic_substitution_in D v \<Longrightarrow> D t \<Longrightarrow> D (logic_subst v t)"
  shows "logic_mgu D a b s"
proof -
  have sd: "logic_substitution_in D s" using small inclusion
    by (auto simp: logic_mgu_def logic_substitution_in_def)
  have se: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b"
    using small unfolding logic_mgu_def by blast
  have re: "logic_atom_map (logic_subst r) a = logic_atom_map (logic_subst r) b"
    using large unfolding logic_mgu_def by blast
  obtain v where vd: "logic_substitution_in E v"
    and factor: "\<And>x. r x = logic_subst v (s x)"
    using small rd re unfolding logic_mgu_def by blast
  have dv: "logic_substitution_in D v" using vd inclusion
    by (auto simp: logic_substitution_in_def)
  have factors: "\<exists>w. logic_substitution_in D w \<and> (\<forall>x. u x = logic_subst w (s x))"
    if ud: "logic_substitution_in D u"
      and ue: "logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u) b" for u
  proof -
    obtain w where wd: "logic_substitution_in D w"
      and wf: "\<And>x. u x = logic_subst w (r x)"
      using large ud ue unfolding logic_mgu_def by blast
    have comp: "logic_substitution_in D (\<lambda>x. logic_subst w (v x))"
      using closed[OF wd] dv by (auto simp: logic_substitution_in_def)
    show ?thesis by (intro exI[of _ "\<lambda>x. logic_subst w (v x)"] conjI comp allI)
      (simp only: wf factor logic_subst_composition)
  qed
  show ?thesis using sd se factors unfolding logic_mgu_def by blast
qed

lemma logic_mgu_arity_extension:
  assumes small: "logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct A t) a b s"
    and exists: "\<exists>r. logic_mgu D a b r"
    and projection: "\<And>t. D t \<Longrightarrow> D (logic_arity_project A z t)"
    and closed: "\<And>v t. logic_substitution_in D v \<Longrightarrow> D t \<Longrightarrow> D (logic_subst v t)"
  shows "logic_mgu D a b s"
proof -
  obtain r where raw: "logic_mgu D a b r" using exists by blast
  have sd: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) s"
    and se: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b"
    using small unfolding logic_mgu_def by blast+
  have typed: "logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct A t) a b r"
    by (rule logic_mgu_restrict_arity[OF raw sd se projection])
  have rd: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) r"
    using typed unfolding logic_mgu_def by blast
  show ?thesis by (rule logic_mgu_domain_extension[OF small raw rd _ closed]) simp
qed

text \<open>Reflection through a substitution-preserving retraction transports
most-generality back to the native representation. Factors are decoded too.\<close>
lemma logic_mgu_encoding_reflect:
  fixes F :: "('f,'v) logic_tree \<Rightarrow> ('g,'v) logic_tree"
    and G :: "('g,'v) logic_tree \<Rightarrow> ('f,'v) logic_tree"
  assumes inverse: "\<And>t. G (F t) = t"
    and forward: "\<And>s t. F (logic_subst s t) = logic_subst (F \<circ> s) (F t)"
    and backward: "\<And>s t. G (logic_subst s t) = logic_subst (G \<circ> s) (G t)"
    and encode: "\<And>t. D t \<Longrightarrow> E (F t)"
    and decode: "\<And>t. E t \<Longrightarrow> D (G t)"
    and mgu: "logic_mgu E (logic_atom_map F a) (logic_atom_map F b) (F \<circ> s)"
  shows "logic_mgu D a b s"
proof -
  have es: "E (F (s x))" for x
    using mgu by (auto simp: logic_mgu_def logic_substitution_in_def)
  have ds: "D (s x)" for x using decode[OF es[of x]] by (simp only: inverse)
  have sd: "logic_substitution_in D s"
    using ds by (simp add: logic_substitution_in_def)
  have eq: "logic_atom_map (logic_subst (F \<circ> s)) (logic_atom_map F a) =
    logic_atom_map (logic_subst (F \<circ> s)) (logic_atom_map F b)"
    using mgu unfolding logic_mgu_def by blast
  have se: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b"
    using arg_cong[OF eq, where f="logic_atom_map G"]
    by (cases a; cases b) (simp add: map_map o_def backward inverse)
  have factors: "\<exists>v. logic_substitution_in D v \<and> (\<forall>x. u x = logic_subst v (s x))"
    if ud: "logic_substitution_in D u"
      and ue: "logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u) b" for u
  proof -
    have ed: "logic_substitution_in E (F \<circ> u)"
      using ud encode by (auto simp: logic_substitution_in_def)
    have ee: "logic_atom_map (logic_subst (F \<circ> u)) (logic_atom_map F a) =
      logic_atom_map (logic_subst (F \<circ> u)) (logic_atom_map F b)"
      using arg_cong[OF ue, where f="logic_atom_map F"]
      by (cases a; cases b) (simp add: map_map o_def forward)
    obtain v where vd: "logic_substitution_in E v"
      and vf: "\<And>x. F (u x) = logic_subst v (F (s x))"
      using mgu ed ee unfolding logic_mgu_def by auto
    have dd: "logic_substitution_in D (G \<circ> v)"
      using vd decode by (auto simp: logic_substitution_in_def)
    have ff: "u x = logic_subst (G \<circ> v) (s x)" for x
      using arg_cong[OF vf[of x], where f=G] by (simp add: backward inverse)
    show ?thesis by (intro exI[of _ "G \<circ> v"] conjI dd allI ff)
  qed
  show ?thesis using sd se factors unfolding logic_mgu_def by blast
qed

lemma cut_rank_mgu_reflect:
  assumes typed: "logic_mgu (\<lambda>t. D (cut_unrank_tree t) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t)
    (logic_atom_map cut_rank_tree a) (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> s)"
    and exists: "\<exists>r. logic_mgu D a b r"
    and projection: "\<And>t. D (cut_unrank_tree t) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree t) = t \<Longrightarrow>
      D (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z t))"
    and closed: "\<And>v t. logic_substitution_in D v \<Longrightarrow> D t \<Longrightarrow> D (logic_subst v t)"
  shows "logic_mgu D a b s"
proof -
  let ?E = "\<lambda>t. D (cut_unrank_tree t) \<and> cut_rank_tree (cut_unrank_tree t) = t"
  obtain r where raw: "logic_mgu D a b r" using exists by blast
  have encoded: "logic_mgu ?E (logic_atom_map cut_rank_tree a)
    (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> r)"
    by (rule cut_rank_image_mgu[OF raw])
  have domains: "(\<lambda>t. ?E t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t) =
    (\<lambda>t. D (cut_unrank_tree t) \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto intro: cut_rank_unrank_tree)
  have project: "?E t \<Longrightarrow> ?E (logic_arity_project (logic_symbol_arity snd) z t)" for t
    using projection by (auto intro: cut_rank_unrank_tree logic_arity_project_correct)
  have subst: "?E (logic_subst v t)" if vd: "logic_substitution_in ?E v" and td: "?E t" for v t
  proof -
    have dv: "logic_substitution_in D (cut_unrank_tree \<circ> v)"
      using vd by (auto simp: logic_substitution_in_def)
    have image_v: "cut_rank_tree \<circ> cut_unrank_tree \<circ> v = v"
      using vd by (auto simp: logic_substitution_in_def fun_eq_iff)
    show ?thesis using closed[OF dv] td
      by (simp add: cut_unrank_subst cut_rank_subst o_assoc image_v)
  qed
  have large: "logic_mgu ?E (logic_atom_map cut_rank_tree a)
    (logic_atom_map cut_rank_tree b) (cut_rank_tree \<circ> s)"
    by (rule logic_mgu_arity_extension[OF _ _ project subst])
      (simp only: domains typed, use encoded in blast)
  show ?thesis by (rule logic_mgu_encoding_reflect[where G=cut_unrank_tree,
      OF cut_unrank_rank_tree cut_rank_subst cut_unrank_subst _ _ large]) simp_all
qed

ML \<open>
  val results = @{thms logic_mgu_domain_extension logic_mgu_arity_extension logic_mgu_encoding_reflect cut_rank_mgu_reflect}
  val _ = if Thm_Deps.has_skip_proof results then error "MGU extension: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "MGU extension: oracle dependency"
\<close>
end
