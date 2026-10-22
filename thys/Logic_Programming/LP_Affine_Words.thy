theory LP_Affine_Words
  imports LP_Pattern_Trace
begin

type_synonym lp_affine = "nat \<times> nat \<times> nat"
fun lp_aeval :: "lp_affine \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lp_aeval (a,b,c) n m = a*n+b*m+c"
fun lp_aadd :: "lp_affine \<Rightarrow> lp_affine \<Rightarrow> lp_affine" where
  "lp_aadd (a,b,c) (d,e,f) = (a+d,b+e,c+f)"
fun lp_ascale :: "nat \<Rightarrow> lp_affine \<Rightarrow> lp_affine" where
  "lp_ascale k (a,b,c) = (k*a,k*b,k*c)"
fun lp_acomp :: "lp_affine \<Rightarrow> lp_affine \<Rightarrow> lp_affine \<Rightarrow> lp_affine" where
  "lp_acomp (a,b,c) u v = lp_aadd (lp_ascale a u) (lp_aadd (lp_ascale b v) (0,0,c))"

lemma lp_aeval_add [simp]: "lp_aeval (lp_aadd a b) n m=lp_aeval a n m+lp_aeval b n m"
  by (cases a; cases b) (simp add: algebra_simps)
lemma lp_aeval_scale [simp]: "lp_aeval (lp_ascale k a) n m=k*lp_aeval a n m"
  by (cases a) (simp add: algebra_simps)
lemma lp_aeval_comp [simp]:
  "lp_aeval (lp_acomp a u v) n m=lp_aeval a (lp_aeval u n m) (lp_aeval v n m)"
  by (cases a) simp

fun lp_word_push :: "'f \<Rightarrow> nat \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> ('f,'v) lp_iterm" where
  "lp_word_push c 0 t=t"
| "lp_word_push c (Suc n) t=LPIFun c [lp_word_push c n t]"
definition lp_word where "lp_word c z n=lp_word_push c n (LPIFun z [])"
lemma lp_word_push_add [simp]:
  "lp_word_push c a (lp_word_push c b t)=lp_word_push c (a+b) t"
  by (induct a) simp_all
lemma lp_word_push_word [simp]: "lp_word_push c a (lp_word c z b)=lp_word c z (a+b)"
  by (simp add: lp_word_def)
lemma lp_word_Suc [simp]: "lp_word c z (Suc n)=LPIFun c [lp_word c z n]"
  by (simp add: lp_word_def)

fun lp_word_term :: "'f \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> ('f,'v) term" where
  "lp_word_term c z 0=Fun z []"
| "lp_word_term c z (Suc n)=Fun c [lp_word_term c z n]"
lemma lp_word_term_sound [simp]: "lp_ieval (lp_word_term c z n) r=lp_word c z n"
  by (induct n) (simp_all add: lp_word_def)
lemma lp_word_term_ground [simp]: "ground (lp_word_term c z n)"
  by (induct n) simp_all

definition lp_alook where "lp_alook env x=the_default (0,0,0) (map_of env x)"
definition lp_aenv where "lp_aenv c z env n m x=lp_word c z (lp_aeval (env x) n m)"

fun lp_word_count :: "'f \<Rightarrow> 'f \<Rightarrow> ('v \<Rightarrow> lp_affine) \<Rightarrow> ('f,'v) term \<Rightarrow> lp_affine option" where
  "lp_word_count c z env (Var x)=Some (env x)"
| "lp_word_count c z env (Fun f [])=(if f=z then Some (0,0,0) else None)"
| "lp_word_count c z env (Fun f [t])=(if f=c then map_option (lp_aadd (0,0,1)) (lp_word_count c z env t) else None)"
| "lp_word_count c z env (Fun f (t#u#ts))=None"

lemma lp_word_count_sound:
  "lp_word_count c z env t=Some a \<Longrightarrow>
    lp_ieval t (lp_aenv c z env n m)=lp_word c z (lp_aeval a n m)"
  by (induct c z env t arbitrary: a rule: lp_word_count.induct)
    (auto simp: lp_aenv_def lp_word_def add.commute split: if_splits option.splits)

fun lp_word_shift :: "'f \<Rightarrow> 'v \<Rightarrow> ('f,'v) term \<Rightarrow> nat option" where
  "lp_word_shift c x (Var y)=(if x=y then Some 0 else None)"
| "lp_word_shift c x (Fun f [t])=(if f=c then map_option Suc (lp_word_shift c x t) else None)"
| "lp_word_shift c x (Fun f [])=None"
| "lp_word_shift c x (Fun f (t#u#ts))=None"

lemma lp_word_shift_sound:
  "lp_word_shift c x t=Some k \<Longrightarrow> lp_ieval t r=lp_word_push c k (r x)"
  by (induct c x t arbitrary: k rule: lp_word_shift.induct)
    (auto split: if_splits option.splits)

lemma lp_word_shift_power:
  assumes "lp_word_shift c x (sig x)=Some k"
  shows "((lp_pattern_env sig^^i) r) x=lp_word_push c (k*i) (r x)"
  by (induct i) (simp_all add: funpow_Suc_right lp_pattern_env_def
      lp_word_shift_sound[OF assms] algebra_simps)

fun lp_word_counts where
  "lp_word_counts c z env []=Some []"
| "lp_word_counts c z env (t#ts)=(case lp_word_count c z env t of None \<Rightarrow> None
    | Some a \<Rightarrow> map_option ((#) a) (lp_word_counts c z env ts))"

lemma lp_word_counts_sound:
  "lp_word_counts c z env ts=Some es \<Longrightarrow>
    map (\<lambda>t. lp_ieval t (lp_aenv c z env n m)) ts = map (\<lambda>a. lp_word c z (lp_aeval a n m)) es"
  by (induct ts arbitrary: es) (auto simp: lp_word_count_sound split: option.splits)

lemma lp_ieval_agree:
  "(\<And>x. x\<in>vars_term t \<Longrightarrow> r x=s x) \<Longrightarrow> lp_ieval t r=lp_ieval t s"
  by (induct t) (auto intro!: map_cong)

lemma lp_atom_eval_agree:
  "(\<And>x. x\<in>set (lp_atom_vars A) \<Longrightarrow> r x=s x) \<Longrightarrow> lp_atom_eval A r=lp_atom_eval A s"
  by (cases A) (auto simp: lp_atom_eval_def lp_atom_vars_def intro!: map_cong lp_ieval_agree)

end
