theory LP_Cut_MGU_Normalize
  imports LP_Cut_Most_General_Source
begin

text \<open>Check a finite solved substitution against both the original
equations and the existing verified normalizer. Merely normalizing is not
enough: cyclic equations can preserve all existing solutions without producing
a solution. The explicit equation check prevents that unsound shortcut.
The factorization theorem quantifies over infinite-tree solutions as well.\<close>

definition lpc_mgu_substitution where
  "lpc_mgu_substitution V images x =
    (case map_of (zip V images) x of None \<Rightarrow> Var x | Some t \<Rightarrow> t)"

definition lpc_check_mgu where
  "lpc_check_mgu fuel equations V images =
    (distinct V \<and> length V = length images \<and>
      lp_cut_normalize fuel equations (map (\<lambda>x. LPCAtom (Var x)) V) =
        Some (Some (map LPCAtom images)) \<and>
      list_all (\<lambda>(s,t). s\<cdot>lpc_mgu_substitution V images =
        t\<cdot>lpc_mgu_substitution V images) equations)"

lemma lpc_mgu_substitution_nth:
  assumes "distinct V" "length V = length images" "i < length V"
  shows "lpc_mgu_substitution V images (V!i) = images!i"
  unfolding lpc_mgu_substitution_def
  using map_of_zip_nth[OF assms(2,1), of i] assms(2,3) by simp

lemma lpc_checked_mgu_unifies:
  assumes "lpc_check_mgu fuel equations V images"
  shows "lp_equations equations (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
  using assms
  by (auto simp: lpc_check_mgu_def lp_equations_def list_all_iff
    case_prod_unfold lp_ieval_finite_subst[symmetric])

lemma lpc_checked_mgu_factor:
  assumes checked: "lpc_check_mgu fuel equations V images"
    and solution: "lp_equations equations \<eta>"
  shows "lp_ieval (lpc_mgu_substitution V images x) \<eta> = \<eta> x"
proof (cases "x\<in>set V")
  case False
  have "length V=length images" using checked by (simp add: lpc_check_mgu_def)
  then have "map_of (zip V images) x = None" using False by simp
  then show ?thesis by (simp add: lpc_mgu_substitution_def)
next
  case True
  then obtain i where i: "i<length V" "V!i=x" by (auto simp: in_set_conv_nth)
  have distinct: "distinct V" and lengths: "length V=length images"
    and normalized: "lp_cut_normalize fuel equations (map (\<lambda>x. LPCAtom (Var x)) V) =
        Some (Some (map LPCAtom images))"
    using checked by (auto simp: lpc_check_mgu_def)
  have maps: "map (\<lambda>t. lp_ieval t \<eta>) images = map \<eta> V"
    using lp_cut_normalized_terms[OF solution, of fuel "map Var V" images] normalized
    by (simp add: map_map o_def)
  have "lp_ieval (images!i) \<eta> = \<eta> (V!i)"
    using arg_cong[OF maps, of "\<lambda>ts. ts!i"] i lengths by simp
  then show ?thesis using lpc_mgu_substitution_nth[OF distinct lengths i(1)] i(2) by simp
qed

theorem lpc_checked_mgu_most_general:
  assumes checked: "lpc_check_mgu fuel equations V images"
    and solution: "lp_equations equations \<eta>"
  shows "\<exists>\<delta>. \<forall>x. lp_isubst
    (lp_ieval (lpc_mgu_substitution V images x) LPIVar) \<delta> = \<eta> x"
  by (rule exI[of _ \<eta>])
    (simp add: lp_ieval_subst lpc_checked_mgu_factor[OF checked solution])

theorem lpc_checked_mgu_unify:
  fixes a b :: "('f,string) term"
  assumes checked: "lpc_check_mgu fuel [(a,b)] V images"
  shows "lpc_mgu_unify (lp_ieval a LPIVar) (lp_ieval b LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
proof -
  let ?s = "\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  have unifies: "lp_isubst (lp_ieval a LPIVar) ?s = lp_isubst (lp_ieval b LPIVar) ?s"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_equations_def lp_ieval_subst)
  have factor: "\<And>\<tau> :: string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a LPIVar) \<tau> = lp_isubst (lp_ieval b LPIVar) \<tau> \<Longrightarrow>
    (\<lambda>x. lp_isubst (?s x) \<tau>) = \<tau>"
  proof -
    fix \<tau> :: "string \<Rightarrow> ('f,string) lp_iterm"
    assume "lp_isubst (lp_ieval a LPIVar) \<tau> = lp_isubst (lp_ieval b LPIVar) \<tau>"
    then have solution: "lp_equations [(a,b)] \<tau>"
      by (simp add: lp_equations_def lp_ieval_subst)
    show "(\<lambda>x. lp_isubst (?s x) \<tau>) = \<tau>"
      by (rule ext) (simp add: lp_ieval_subst lpc_checked_mgu_factor[OF checked solution])
  qed
  show ?thesis
    unfolding lpc_mgu_unify_def
    apply (intro conjI)
     apply (rule unifies)
    apply (intro allI impI)
    subgoal for \<tau>
      apply (rule exI[of _ \<tau>])
      apply (simp add: lpc_isubst_comp factor map_map o_def lp_cut_map_comp)
      done
    done
qed

theorem lpc_checked_mgu_resolve:
  fixes a h :: "('f,string) term"
  assumes checked: "lpc_check_mgu fuel [(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))] V images"
    and short_a: "\<forall>x\<in>vars_term a. length x<k"
    and short_gs: "lp_cut_short_goals k gs"
  shows "lpc_mgu_resolve (lp_ieval a LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images (lp_prefix k x)) LPIVar)"
proof -
  let ?s = "\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  let ?r = "\<lambda>x. ?s (lp_prefix k x)"
  let ?eqs = "[(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))]"
  have unifies: "lp_isubst (lp_ieval a LPIVar) ?s = lp_ieval h ?r"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_equations_def lp_ieval_subst lp_ieval_finite_subst)
  have factor: "\<And>\<tau> \<nu> :: string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a LPIVar) \<tau> = lp_ieval h \<nu> \<Longrightarrow>
    \<exists>\<delta>.
      lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) \<delta> = lp_isubst (lp_ieval a LPIVar) \<tau> \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) \<delta>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
  proof -
    fix \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
    assume comparison: "lp_isubst (lp_ieval a LPIVar) \<tau> = lp_ieval h \<nu>"
    let ?d = "\<lambda>x. if length x<k then \<tau> x else \<nu> (drop k x)"
    have fresh: "\<And>x. ?d (lp_prefix k x) = \<nu> x" by (simp add: lp_prefix_def)
    have old: "\<And>t. (\<forall>x\<in>vars_term t. length x<k) \<Longrightarrow> lp_ieval t ?d = lp_ieval t \<tau>"
      by (rule lp_ieval_cong) auto
    have solution: "lp_equations ?eqs ?d"
      using comparison old[OF short_a]
      by (simp add: lp_equations_def lp_ieval_finite_subst lp_ieval_subst fresh)
    have composed: "(\<lambda>x. lp_isubst (?s x) ?d) = ?d"
      by (rule ext) (simp add: lp_ieval_subst lpc_checked_mgu_factor[OF checked solution])
    have composed_eval: "(\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) ?d) = ?d"
      using composed by (simp add: lp_ieval_subst)
    have active: "\<And>t. (\<forall>x\<in>vars_term t. length x<k) \<Longrightarrow>
      lp_isubst (lp_isubst (lp_ieval t LPIVar) ?s) ?d = lp_isubst (lp_ieval t LPIVar) \<tau>"
      by (simp add: lp_ieval_subst composed_eval old)
    show "\<exists>\<delta>.
      lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) \<delta> = lp_isubst (lp_ieval a LPIVar) \<tau> \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) \<delta>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    proof (rule exI[of _ ?d], intro conjI)
      show "lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) ?d = lp_isubst (lp_ieval a LPIVar) \<tau>"
        by (rule active[OF short_a])
      show "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) ?d))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
        map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)"
        unfolding map_map o_def lp_cut_map_comp
        by (rule map_cong[OF refl], rule lp_cut_goal_map_cong, rule active)
          (use short_gs in \<open>auto simp: lp_cut_short_goals_def\<close>)
      show "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) ?d)) bs =
        map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
      proof -
        have "(\<lambda>x. lp_isubst (?r x) ?d) = \<nu>"
          using fun_cong[OF composed, of "lp_prefix k _"] by (auto simp: fresh)
        then show ?thesis by (simp add: lp_ieval_subst)
      qed
    qed
  qed
  show ?thesis unfolding lpc_mgu_resolve_def using unifies factor by blast
qed

lemma lpc_checked_mgu_simple_positive:
  "lpc_check_mgu 4 [(Var x, Fun f [])] [x] [Fun f []]"
  by (simp add: lpc_check_mgu_def lp_cut_normalize_def lpc_mgu_substitution_def
    lp_atom_subst_def lp_normalize_goals_code)

lemma lpc_checked_mgu_rejects_cyclic_finite_candidate:
  "\<not>lpc_check_mgu 4 [(Var x, Fun f [Var x])] [x] [Fun f [Var x]]"
  by (simp add: lpc_check_mgu_def lpc_mgu_substitution_def)

text \<open>These checks are foundations for the precise source connection;
they do not change the currently exported accepting checker.\<close>

end
