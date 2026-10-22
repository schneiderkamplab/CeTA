theory LP_Affine_Success
  imports LP_Affine_Words
begin

definition lp_word_atom where
  "lp_word_atom c z env A=map_option (Pair (fst A)) (lp_word_counts c z env (snd A))"
lemma lp_word_atom_sound:
  "lp_word_atom c z env A=Some (f,es) \<Longrightarrow>
    lp_atom_eval A (lp_aenv c z env n m)=(f,map (\<lambda>a. lp_word c z (lp_aeval a n m)) es)"
  by (cases A) (auto simp: lp_word_atom_def lp_atom_eval_def lp_word_counts_sound split: option.splits)

definition lp_summary_image where
  "lp_summary_image c z sig mu rho idx x =
    (case lp_word_shift c x (mk_subst Var sig x) of None \<Rightarrow> None | Some k \<Rightarrow>
      map_option (lp_aadd (lp_ascale k idx)) (lp_word_count c z rho (mk_subst Var mu x)))"
definition lp_summary_env where
  "lp_summary_env c z sig mu rho idx x=the_default (0,0,0) (lp_summary_image c z sig mu rho idx x)"

lemma lp_summary_image_sound:
  assumes image: "lp_summary_image c z sig mu rho idx x=Some a"
  shows "((lp_pattern_env (mk_subst Var sig)^^lp_aeval idx n m)
      (lp_pattern_env (mk_subst Var mu) (lp_aenv c z rho n m))) x =
    lp_word c z (lp_aeval a n m)"
proof -
  obtain k e where shift: "lp_word_shift c x (mk_subst Var sig x)=Some k"
    and count: "lp_word_count c z rho (mk_subst Var mu x)=Some e"
    and a: "a=lp_aadd (lp_ascale k idx) e"
    using image by (auto simp: lp_summary_image_def split: option.splits)
  show ?thesis by (simp add: lp_word_shift_power[where sig="mk_subst Var sig", OF shift] lp_pattern_env_def
      lp_word_count_sound[OF count] a)
qed

definition lp_affine_success_check where
  "lp_affine_success_check P c z env A B sig mu tsb nu basetrace steps idx rho =
    (lp_success_pattern_check P B sig tsb mu nu basetrace steps \<and>
     list_all (\<lambda>x. lp_summary_image c z sig mu rho idx x\<noteq>None) (lp_atom_vars B) \<and>
     (case lp_word_atom c z env A of None \<Rightarrow> False | Some es \<Rightarrow>
       lp_word_atom c z (lp_summary_env c z sig mu rho idx) B=Some es))"

theorem lp_affine_success_sound:
  assumes ok: "lp_affine_success_check P c z env A B sig mu tsb nu basetrace steps idx rho"
  shows "(lp_atom_eval A (lp_aenv c z env n m)#tail,tail)\<in>(lp_ild P)\<^sup>*"
proof -
  have checked: "lp_success_pattern_check P B sig tsb mu nu basetrace steps"
    and images: "\<And>x. x\<in>set (lp_atom_vars B) \<Longrightarrow> lp_summary_image c z sig mu rho idx x\<noteq>None"
    using ok by (auto simp: lp_affine_success_check_def list_all_iff)
  obtain f es where lhs: "lp_word_atom c z env A=Some (f,es)"
    and rhs: "lp_word_atom c z (lp_summary_env c z sig mu rho idx) B=Some (f,es)"
    using ok by (auto simp: lp_affine_success_check_def split: option.splits)
  let ?r = "(lp_pattern_env (mk_subst Var sig)^^lp_aeval idx n m)
      (lp_pattern_env (mk_subst Var mu) (lp_aenv c z rho n m))"
  have env: "\<And>x. x\<in>set (lp_atom_vars B) \<Longrightarrow>
      ?r x=lp_aenv c z (lp_summary_env c z sig mu rho idx) n m x"
  proof -
    fix x assume member: "x\<in>set (lp_atom_vars B)"
    obtain a where image: "lp_summary_image c z sig mu rho idx x=Some a"
      using images[OF member] by (cases "lp_summary_image c z sig mu rho idx x") auto
    show "?r x=lp_aenv c z (lp_summary_env c z sig mu rho idx) n m x"
      using lp_summary_image_sound[OF image, of n m]
      by (simp add: lp_summary_env_def lp_aenv_def image)
  qed
  have agree: "lp_atom_eval B ?r=lp_atom_eval B (lp_aenv c z (lp_summary_env c z sig mu rho idx) n m)"
    by (rule lp_atom_eval_agree) (rule env)
  have equal: "lp_atom_eval A (lp_aenv c z env n m)=lp_atom_eval B ?r"
  proof -
    have "lp_atom_eval A (lp_aenv c z env n m)=(f,map (\<lambda>a. lp_word c z (lp_aeval a n m)) es)"
      by (rule lp_word_atom_sound[OF lhs])
    also have "...=lp_atom_eval B (lp_aenv c z (lp_summary_env c z sig mu rho idx) n m)"
      by (rule sym, rule lp_word_atom_sound[OF rhs])
    also have "...=lp_atom_eval B ?r" by (rule sym, rule agree)
    finally show ?thesis .
  qed
  show ?thesis unfolding equal
    by (rule lp_success_pattern_check_sound[OF checked])
qed

end
