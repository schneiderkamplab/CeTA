theory LP_Finite_Affine_Success
  imports LP_Finite_Affine_Words
begin

lemma lp_finite_word_atom_sound:
  "lp_word_atom c z env A=Some (f,es) \<Longrightarrow>
    lp_finite_atom_eval A (lp_finite_aenv c z env n m)=(f,map (\<lambda>a. lp_finite_word c z (lp_aeval a n m)) es)"
  by (cases A) (auto simp: lp_word_atom_def lp_atom_subst_def lp_finite_word_counts_sound split: option.splits)


lemma lp_finite_summary_image_sound:
  assumes image: "lp_summary_image c z sig mu rho idx x=Some a"
  shows "((lp_finite_pattern_env (mk_subst Var sig)^^lp_aeval idx n m)
      (lp_finite_pattern_env (mk_subst Var mu) (lp_finite_aenv c z rho n m))) x =
    lp_finite_word c z (lp_aeval a n m)"
proof -
  obtain k e where shift: "lp_word_shift c x (mk_subst Var sig x)=Some k"
    and count: "lp_word_count c z rho (mk_subst Var mu x)=Some e"
    and a: "a=lp_aadd (lp_ascale k idx) e"
    using image by (auto simp: lp_summary_image_def split: option.splits)
  show ?thesis by (simp add: lp_finite_word_shift_power[where sig="mk_subst Var sig", OF shift] lp_finite_pattern_env_def
      lp_finite_word_count_sound[OF count] a)
qed


theorem lp_finite_affine_success_sound:
  assumes ok: "lp_affine_success_check P c z env A B sig mu tsb nu basetrace steps idx rho"
  shows "(lp_finite_atom_eval A (lp_finite_aenv c z env n m)#tail,tail)\<in>(lp_ld P)\<^sup>*"
proof -
  have checked: "lp_success_pattern_check P B sig tsb mu nu basetrace steps"
    and images: "\<And>x. x\<in>set (lp_atom_vars B) \<Longrightarrow> lp_summary_image c z sig mu rho idx x\<noteq>None"
    using ok by (auto simp: lp_affine_success_check_def list_all_iff)
  obtain f es where lhs: "lp_word_atom c z env A=Some (f,es)"
    and rhs: "lp_word_atom c z (lp_summary_env c z sig mu rho idx) B=Some (f,es)"
    using ok by (auto simp: lp_affine_success_check_def split: option.splits)
  let ?r = "(lp_finite_pattern_env (mk_subst Var sig)^^lp_aeval idx n m)
      (lp_finite_pattern_env (mk_subst Var mu) (lp_finite_aenv c z rho n m))"
  have env: "\<And>x. x\<in>set (lp_atom_vars B) \<Longrightarrow>
      ?r x=lp_finite_aenv c z (lp_summary_env c z sig mu rho idx) n m x"
  proof -
    fix x assume member: "x\<in>set (lp_atom_vars B)"
    obtain a where image: "lp_summary_image c z sig mu rho idx x=Some a"
      using images[OF member] by (cases "lp_summary_image c z sig mu rho idx x") auto
    show "?r x=lp_finite_aenv c z (lp_summary_env c z sig mu rho idx) n m x"
      using lp_finite_summary_image_sound[OF image, of n m]
      by (simp add: lp_summary_env_def lp_finite_aenv_def image)
  qed
  have agree: "lp_finite_atom_eval B ?r=lp_finite_atom_eval B (lp_finite_aenv c z (lp_summary_env c z sig mu rho idx) n m)"
    by (rule lp_finite_atom_eval_agree) (rule env)
  have equal: "lp_finite_atom_eval A (lp_finite_aenv c z env n m)=lp_finite_atom_eval B ?r"
  proof -
    have "lp_finite_atom_eval A (lp_finite_aenv c z env n m)=(f,map (\<lambda>a. lp_finite_word c z (lp_aeval a n m)) es)"
      by (rule lp_finite_word_atom_sound[OF lhs])
    also have "...=lp_finite_atom_eval B (lp_finite_aenv c z (lp_summary_env c z sig mu rho idx) n m)"
      by (rule sym, rule lp_finite_word_atom_sound[OF rhs])
    also have "...=lp_finite_atom_eval B ?r" by (rule sym, rule agree)
    finally show ?thesis .
  qed
  show ?thesis unfolding equal
    by (rule lp_finite_success_pattern_check_sound[OF checked])
qed


end
