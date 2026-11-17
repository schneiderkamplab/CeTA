theory LP_Cut_MGU_Erasure
  imports LP_Cut_Extended_MGU
begin

text \<open>This proof interface states transport of a typed global MGU to
native terms. The three concrete instances below discharge it; it is not an
assumption on accepted certificates.\<close>
definition cut_mgu_erasure :: "(('f lp_cut_symbol,string) lp_iterm \<Rightarrow> bool) \<Rightarrow> bool" where
  "cut_mgu_erasure D \<longleftrightarrow> (\<forall>a b s.
    logic_tree_arity_correct (logic_symbol_arity snd) a \<longrightarrow>
    logic_tree_arity_correct (logic_symbol_arity snd) b \<longrightarrow>
    logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) (LAtom () [a]) (LAtom () [b]) s \<longrightarrow>
    lp_runtime_mgu D ((),[cut_tree (cut_unrank_tree a)]) ((),[cut_tree (cut_unrank_tree b)])
      (cut_tree \<circ> cut_unrank_tree \<circ> s))"

lemma cut_finite_mgu_erasure: "cut_mgu_erasure (cut_finite_runtime :: ('f lp_cut_symbol,string) lp_iterm \<Rightarrow> bool)"
proof (unfold cut_mgu_erasure_def, intro allI impI)
  fix a b :: "(('f \<times> nat) logic_symbol,string) logic_tree"
    and s :: "string \<Rightarrow> (('f \<times> nat) logic_symbol,string) logic_tree"
  assume ca: "logic_tree_arity_correct (logic_symbol_arity snd) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity snd) b"
    and mgu: "logic_mgu (\<lambda>t. cut_finite_runtime (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) (LAtom () [a]) (LAtom () [b]) s"
  have domains: "(\<lambda>t. cut_finite_runtime (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) =
    (\<lambda>t. logic_finite t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto simp: cut_finite_domain_iff cut_typed_unrank_finite)
  have erased: "logic_mgu (\<lambda>t. cut_finite_runtime (cut_tree t))
    (LAtom () [cut_unrank_tree a]) (LAtom () [cut_unrank_tree b]) (cut_unrank_tree \<circ> s)"
    using cut_unrank_finite_mgu[OF mgu[unfolded domains]] ca cb
    by (simp add: cut_finite_domain_iff)
  show "lp_runtime_mgu cut_finite_runtime ((),[cut_tree (cut_unrank_tree a)]) ((),[cut_tree (cut_unrank_tree b)])
      (cut_tree \<circ> cut_unrank_tree \<circ> s)"
    using cut_tree_native.mgu_iff[where D=cut_finite_runtime, THEN iffD1, OF erased]
    by (simp add: o_assoc)
qed

lemma cut_rational_mgu_erasure: "cut_mgu_erasure (cut_rational_runtime :: ('f lp_cut_symbol,string) lp_iterm \<Rightarrow> bool)"
proof (unfold cut_mgu_erasure_def, intro allI impI)
  fix a b :: "(('f \<times> nat) logic_symbol,string) logic_tree"
    and s :: "string \<Rightarrow> (('f \<times> nat) logic_symbol,string) logic_tree"
  assume ca: "logic_tree_arity_correct (logic_symbol_arity snd) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity snd) b"
    and mgu: "logic_mgu (\<lambda>t. cut_rational_runtime (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) (LAtom () [a]) (LAtom () [b]) s"
  have domains: "(\<lambda>t. cut_rational_runtime (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) =
    (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto simp: cut_rational_runtime_def cut_typed_unrank_rational)
  have erased: "logic_mgu (\<lambda>t. cut_rational_runtime (cut_tree t))
    (LAtom () [cut_unrank_tree a]) (LAtom () [cut_unrank_tree b]) (cut_unrank_tree \<circ> s)"
    using cut_unrank_rational_mgu[OF mgu[unfolded domains]] ca cb
    by (simp add: cut_rational_runtime_def)
  show "lp_runtime_mgu cut_rational_runtime ((),[cut_tree (cut_unrank_tree a)]) ((),[cut_tree (cut_unrank_tree b)])
      (cut_tree \<circ> cut_unrank_tree \<circ> s)"
    using cut_tree_native.mgu_iff[where D=cut_rational_runtime, THEN iffD1, OF erased]
    by (simp add: o_assoc)
qed

lemma cut_infinite_mgu_erasure: "cut_mgu_erasure (\<lambda>(_ :: ('f lp_cut_symbol,string) lp_iterm). True)"
proof (unfold cut_mgu_erasure_def, intro allI impI)
  fix a b :: "(('f \<times> nat) logic_symbol,string) logic_tree"
    and s :: "string \<Rightarrow> (('f \<times> nat) logic_symbol,string) logic_tree"
  assume ca: "logic_tree_arity_correct (logic_symbol_arity snd) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity snd) b"
    and mgu: "logic_mgu (\<lambda>t. True \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)
      (LAtom () [a]) (LAtom () [b]) s"
  have erased: "logic_mgu (\<lambda>t. True) (LAtom () [cut_unrank_tree a])
    (LAtom () [cut_unrank_tree b]) (cut_unrank_tree \<circ> s)"
    using cut_unrank_infinite_mgu[where a="LAtom () [a]" and b="LAtom () [b]" and s=s] mgu ca cb by simp
  show "lp_runtime_mgu (\<lambda>_. True) ((),[cut_tree (cut_unrank_tree a)]) ((),[cut_tree (cut_unrank_tree b)])
      (cut_tree \<circ> cut_unrank_tree \<circ> s)"
    using cut_tree_native.mgu_iff[where D="\<lambda>_. True", THEN iffD1, OF erased]
    by (simp add: o_assoc)
qed

context cut_runtime_domain
begin
lemma erased_mgu_unify:
  assumes erasure: "cut_mgu_erasure D"
    and ca: "logic_tree_arity_correct (logic_symbol_arity snd) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity snd) b"
    and mgu: "logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) (LAtom () [a]) (LAtom () [b]) s"
  shows "mgu_unify (cut_tree (cut_unrank_tree a)) (cut_tree (cut_unrank_tree b)) gs
    (cut_tree \<circ> cut_unrank_tree \<circ> s)"
proof -
  let ?s = "cut_tree \<circ> cut_unrank_tree \<circ> s"
  let ?a = "cut_tree (cut_unrank_tree a)"
  let ?b = "cut_tree (cut_unrank_tree b)"
  have native: "lp_runtime_mgu D ((),[?a]) ((),[?b]) ?s"
    using erasure ca cb mgu unfolding cut_mgu_erasure_def by blast
  have eq: "lp_isubst ?a ?s = lp_isubst ?b ?s" and sd: "\<forall>x. D (?s x)"
    using native by (auto simp: lp_runtime_mgu_def lp_iatom_subst_def)
  have factor: "\<exists>delta. (\<forall>x. D (delta x)) \<and>
      lp_isubst (lp_isubst ?a ?s) delta = lp_isubst ?a u \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) delta)) gs =
        map (lp_cut_map (\<lambda>t. lp_isubst t u)) gs"
    if ud: "\<forall>x. D (u x)" and ue: "lp_isubst ?a u = lp_isubst ?b u" for u
  proof -
    obtain delta where dd: "\<forall>x. D (delta x)"
      and df: "\<forall>x. u x = lp_isubst (?s x) delta"
      using native ud ue unfolding lp_runtime_mgu_def lp_iatom_subst_def by auto
    have comp: "(\<lambda>x. lp_isubst (?s x) delta) = u" using df by auto
    show ?thesis by (intro exI[of _ delta]) (simp only: dd lpc_isubst_comp comp simp_thms)
  qed
  show ?thesis using eq sd factor unfolding mgu_unify_def by blast
qed
end

ML \<open>
  val results = @{thms cut_finite_mgu_erasure cut_rational_mgu_erasure cut_infinite_mgu_erasure cut_runtime_domain.erased_mgu_unify}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut MGU erasure: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Cut MGU erasure: oracle dependency"
\<close>
end
