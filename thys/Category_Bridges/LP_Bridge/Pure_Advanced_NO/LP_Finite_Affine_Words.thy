theory LP_Finite_Affine_Words
  imports LP_Finite_Pattern_Acceleration
begin

fun lp_finite_word_push :: "'f \<Rightarrow> nat \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term" where
  "lp_finite_word_push c 0 t=t"
| "lp_finite_word_push c (Suc n) t=Fun c [lp_finite_word_push c n t]"

definition lp_finite_word where "lp_finite_word c z n=lp_finite_word_push c n (Fun z [])"

lemma lp_finite_word_push_add [simp]:
  "lp_finite_word_push c a (lp_finite_word_push c b t)=lp_finite_word_push c (a+b) t"
  by (induct a) simp_all

lemma lp_finite_word_push_word [simp]: "lp_finite_word_push c a (lp_finite_word c z b)=lp_finite_word c z (a+b)"
  by (simp add: lp_finite_word_def)

lemma lp_finite_word_Suc [simp]: "lp_finite_word c z (Suc n)=Fun c [lp_finite_word c z n]"
  by (simp add: lp_finite_word_def)


lemma lp_finite_word_eq_term: "lp_finite_word c z n=lp_word_term c z n"
  by (induct n) (simp_all add: lp_finite_word_def)

lemma lp_finite_word_term_sound [simp]: "lp_finite_eval (lp_word_term c z n) r=lp_finite_word c z n"
  by (induct n) (simp_all add: lp_finite_word_def)

definition lp_finite_aenv where "lp_finite_aenv c z env n m x=lp_finite_word c z (lp_aeval (env x) n m)"


lemma lp_finite_word_count_sound:
  "lp_word_count c z env t=Some a \<Longrightarrow>
    lp_finite_eval t (lp_finite_aenv c z env n m)=lp_finite_word c z (lp_aeval a n m)"
  by (induct c z env t arbitrary: a rule: lp_word_count.induct)
    (auto simp: lp_finite_aenv_def lp_finite_word_def add.commute split: if_splits option.splits)


lemma lp_finite_word_shift_sound:
  "lp_word_shift c x t=Some k \<Longrightarrow> lp_finite_eval t r=lp_finite_word_push c k (r x)"
  by (induct c x t arbitrary: k rule: lp_word_shift.induct)
    (auto split: if_splits option.splits)


lemma lp_finite_word_shift_power:
  assumes "lp_word_shift c x (sig x)=Some k"
  shows "((lp_finite_pattern_env sig^^i) r) x=lp_finite_word_push c (k*i) (r x)"
  by (induct i) (simp_all add: funpow_Suc_right lp_finite_pattern_env_def
      lp_finite_word_shift_sound[OF assms] algebra_simps)


lemma lp_finite_word_counts_sound:
  "lp_word_counts c z env ts=Some es \<Longrightarrow>
    map (\<lambda>t. lp_finite_eval t (lp_finite_aenv c z env n m)) ts = map (\<lambda>a. lp_finite_word c z (lp_aeval a n m)) es"
  by (induct ts arbitrary: es) (auto simp: lp_finite_word_count_sound split: option.splits)


lemma lp_finite_ieval_agree:
  "(\<And>x. x\<in>vars_term t \<Longrightarrow> r x=s x) \<Longrightarrow> lp_finite_eval t r=lp_finite_eval t s"
  by (induct t) (auto intro!: map_cong)


lemma lp_finite_atom_eval_agree:
  "(\<And>x. x\<in>set (lp_atom_vars A) \<Longrightarrow> r x=s x) \<Longrightarrow> lp_finite_atom_eval A r=lp_finite_atom_eval A s"
  by (cases A) (auto simp: lp_atom_subst_def lp_atom_vars_def intro!: map_cong lp_finite_ieval_agree)


end
