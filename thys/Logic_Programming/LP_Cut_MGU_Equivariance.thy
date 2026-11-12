theory LP_Cut_MGU_Equivariance
 imports LP_Cut_MGU_Normalize
begin

text \<open>The checked solved substitution has a global factorization property,
including variables that occur only in a delayed continuation. Conjugating it
by an involution preserves that property. No assumption about the normalizer's
choice of variable names is needed.\<close>

definition lpc_global_mgu :: "(('f,'v) term \<times> ('f,'v) term) list \<Rightarrow> ('v \<Rightarrow> ('f,'v) term) \<Rightarrow> bool" where
 "lpc_global_mgu E s =
   (lp_equations E (\<lambda>x. lp_ieval (s x) LPIVar) \<and>
    (\<forall>eta :: 'v \<Rightarrow> ('f,'v) lp_iterm. lp_equations E eta \<longrightarrow> (\<forall>x. lp_ieval (s x) eta = eta x)))"

lemma lpc_checked_global_mgu:
 assumes checked: "lpc_check_mgu fuel E V images"
 shows "lpc_global_mgu E (lpc_mgu_substitution V images)"
 unfolding lpc_global_mgu_def
 proof (intro conjI allI impI)
  show "lp_equations E (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
    by (rule lpc_checked_mgu_unifies[OF checked])
 next
  fix eta x
  assume "lp_equations E eta"
  then show "lp_ieval (lpc_mgu_substitution V images x) eta = eta x"
    by (rule lpc_checked_mgu_factor[OF checked])
 qed

lemma lpc_global_mgu_unifies:
 "lpc_global_mgu E s \<Longrightarrow> lp_equations E (\<lambda>x. lp_ieval (s x) LPIVar)"
 by (simp add: lpc_global_mgu_def)

lemma lpc_global_mgu_factor:
 fixes E :: "(('f,'v) term \<times> ('f,'v) term) list"
   and eta :: "'v \<Rightarrow> ('f,'v) lp_iterm"
 assumes "lpc_global_mgu E s" "lp_equations E eta"
 shows "lp_ieval (s x) eta = eta x"
 using assms by (simp add: lpc_global_mgu_def)

definition lpc_rename_equations where
 "lpc_rename_equations p E = map (\<lambda>(a,b). (a\<cdot>(Var \<circ> p), b\<cdot>(Var \<circ> p))) E"

definition lpc_conjugate_substitution where
 "lpc_conjugate_substitution p s x = (s (p x))\<cdot>(Var \<circ> p)"

lemma lpc_rename_equations_solution:
 "lp_equations (lpc_rename_equations p E) eta = lp_equations E (eta \<circ> p)"
 by (auto simp: lpc_rename_equations_def lp_equations_def list_all_iff lp_ieval_finite_subst o_def)

lemma lpc_global_mgu_conjugate:
 fixes E :: "(('f,'v) term \<times> ('f,'v) term) list"
 assumes mgu: "lpc_global_mgu E s" and inverse: "\<And>x. p (p x) = x"
 shows "lpc_global_mgu (lpc_rename_equations p E) (lpc_conjugate_substitution p s)"
proof -
 have unifies: "lp_equations E (\<lambda>x. lp_ieval (s x) LPIVar)"
   using mgu by (simp add: lpc_global_mgu_def)
 have factor: "\<And>(eta :: 'v \<Rightarrow> ('f,'v) lp_iterm) x. lp_equations E eta \<Longrightarrow> lp_ieval (s x) eta = eta x"
   using mgu by (simp add: lpc_global_mgu_def)
 have renamed_unifies: "lp_equations (lpc_rename_equations p E)
    (\<lambda>x. lp_ieval (lpc_conjugate_substitution p s x) LPIVar)"
 proof -
   have eq: "lp_ieval a (\<lambda>x. lp_ieval (s x) (LPIVar \<circ> p)) =
             lp_ieval b (\<lambda>x. lp_ieval (s x) (LPIVar \<circ> p))"
     if "(a,b) \<in> set E" for a b
   proof -
     have base: "lp_ieval a (\<lambda>x. lp_ieval (s x) LPIVar) =
       lp_ieval b (\<lambda>x. lp_ieval (s x) LPIVar)"
       using unifies that by (auto simp: lp_equations_def list_all_iff)
     note mapped = arg_cong[OF base, of "\<lambda>t. lp_isubst t (LPIVar \<circ> p)"]
     show ?thesis using mapped by (simp add: lp_ieval_subst o_def)
   qed
   show ?thesis
     unfolding lpc_rename_equations_solution
     by (auto simp: lpc_conjugate_substitution_def
       lp_ieval_finite_subst o_def inverse lp_equations_def list_all_iff intro: eq[unfolded o_def])
 qed
 have renamed_factor: "lp_ieval (lpc_conjugate_substitution p s x) eta = eta x"
   if solution: "lp_equations (lpc_rename_equations p E) eta" for eta :: "'v \<Rightarrow> ('f,'v) lp_iterm" and x
   using factor[of "eta \<circ> p" "p x"] solution
   by (simp add: lpc_rename_equations_solution lpc_conjugate_substitution_def
     lp_ieval_finite_subst o_def inverse)
 show ?thesis using renamed_unifies renamed_factor
   unfolding lpc_global_mgu_def by blast
qed

theorem lpc_global_mgu_unify:
  fixes a b :: "('f,string) term"
  assumes checked: "lpc_global_mgu [(a,b)] substitution"
  shows "lpc_mgu_unify (lp_ieval a LPIVar) (lp_ieval b LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)
    (\<lambda>x. lp_ieval (substitution x) LPIVar)"
proof -
  let ?s = "\<lambda>x. lp_ieval (substitution x) LPIVar"
  have unifies: "lp_isubst (lp_ieval a LPIVar) ?s = lp_isubst (lp_ieval b LPIVar) ?s"
    using lpc_global_mgu_unifies[OF checked]
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
      by (rule ext) (simp add: lp_ieval_subst lpc_global_mgu_factor[OF checked solution])
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

ML \<open>
val checked = [@{thm lpc_checked_global_mgu}, @{thm lpc_global_mgu_conjugate}, @{thm lpc_global_mgu_unify}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted MGU equivariance dependency" else ();
\<close>
end
