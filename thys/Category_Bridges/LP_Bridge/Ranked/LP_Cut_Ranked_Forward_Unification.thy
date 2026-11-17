theory LP_Cut_Ranked_Forward_Unification
  imports Category_LP_Cut_NO_Bridge.LP_Cut_Ranked_Resolution
begin

text \<open>A native unifier can be ranked and projected to the correct arities.
Consequently failure in the ranked semantics implies native failure; this is
proved for unification, not assumed as a termination-restriction principle.\<close>
lemma cut_rank_typed_fresh_unifier:
  assumes fresh: "logic_freshening r
      (logic_arguments (cut_rank_runtime_atom a) @ active)
      (logic_arguments (cut_rank_atom h) @ body)"
    and caller: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (cut_rank_runtime_atom a))"
    and clause: "list_all (arity_correct (logic_symbol_arity snd))
      (logic_arguments (cut_rank_atom h))"
    and sd: "logic_substitution_in D s" and td: "logic_substitution_in D t"
    and projection: "\<And>u. D (cut_unrank_tree u) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z u))"
    and equation: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval t) h"
  shows "\<exists>u. logic_substitution_in (\<lambda>t. D (cut_unrank_tree t) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) u \<and>
    logic_atom_map (logic_subst u) (cut_rank_runtime_atom a) =
      logic_atom_map (logic_subst u \<circ> logic_eval (LVar \<circ> r)) (cut_rank_atom h)"
proof -
  let ?E = "\<lambda>u. D (cut_unrank_tree u) \<and> cut_rank_tree (cut_unrank_tree u) = u"
  have rs: "logic_substitution_in ?E (cut_rank_tree \<circ> s)"
    and rt: "logic_substitution_in ?E (cut_rank_tree \<circ> t)"
    using sd td by (simp_all add: logic_substitution_in_def)
  have closed: "?E u \<Longrightarrow> ?E (logic_arity_project (logic_symbol_arity snd) z u)" for u
    using projection by (auto intro: cut_rank_unrank_tree logic_arity_project_correct)
  have ranked: "logic_atom_map (logic_subst (cut_rank_tree \<circ> s)) (cut_rank_runtime_atom a) =
      logic_atom_map (logic_eval (cut_rank_tree \<circ> t)) (cut_rank_atom h)"
    using arg_cong[OF equation, where f=cut_rank_runtime_atom]
    by (simp only: cut_rank_runtime_atom_subst cut_rank_atom_eval)
  obtain u where domain: "logic_substitution_in (\<lambda>u. ?E u \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) u) u"
    and unifies: "logic_atom_map (logic_subst u) (cut_rank_runtime_atom a) =
      logic_atom_map (logic_subst u \<circ> logic_eval (LVar \<circ> r)) (cut_rank_atom h)"
    using logic_typed_fresh_unifier[OF fresh caller clause rs rt closed ranked] by blast
  show ?thesis by (rule exI[of _ u])
    (use domain unifies in \<open>auto simp: logic_substitution_in_def\<close>)
qed

lemma cut_rank_typed_equalizer:
  assumes left: "logic_tree_arity_correct (logic_symbol_arity snd) (cut_rank_tree a)"
    and right: "logic_tree_arity_correct (logic_symbol_arity snd) (cut_rank_tree b)"
    and sd: "logic_substitution_in D s"
    and projection: "\<And>u. D (cut_unrank_tree u) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z u))"
    and equation: "logic_subst s a = logic_subst s b"
  shows "\<exists>u. logic_substitution_in (\<lambda>t. D (cut_unrank_tree t) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) u \<and>
    logic_subst u (cut_rank_tree a) = logic_subst u (cut_rank_tree b)"
proof -
  let ?E = "\<lambda>u. D (cut_unrank_tree u) \<and> cut_rank_tree (cut_unrank_tree u) = u"
  have rs: "logic_substitution_in ?E (cut_rank_tree \<circ> s)"
    using sd by (simp add: logic_substitution_in_def)
  have closed: "?E u \<Longrightarrow> ?E (logic_arity_project (logic_symbol_arity snd) z u)" for u
    using projection by (auto intro: cut_rank_unrank_tree logic_arity_project_correct)
  have ranked: "logic_subst (cut_rank_tree \<circ> s) (cut_rank_tree a) =
      logic_subst (cut_rank_tree \<circ> s) (cut_rank_tree b)"
    using arg_cong[OF equation, where f=cut_rank_tree] by (simp only: cut_rank_subst)
  have exists: "\<exists>u. logic_substitution_in ?E u \<and>
      logic_subst u (cut_rank_tree a) = logic_subst u (cut_rank_tree b)"
    using rs ranked by blast
  obtain u where domain: "logic_substitution_in (\<lambda>u. ?E u \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) u) u"
    and unifies: "logic_subst u (cut_rank_tree a) = logic_subst u (cut_rank_tree b)"
    using logic_arity_unifiable_iff[where D="?E" and z=z, OF left right closed] exists by blast
  show ?thesis by (rule exI[of _ u])
    (use domain unifies in \<open>auto simp: logic_substitution_in_def\<close>)
qed

ML \<open>
  val results = @{thms cut_rank_typed_fresh_unifier cut_rank_typed_equalizer}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked unification: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Ranked unification: oracle dependency"
\<close>
end
