theory LP_Prolog_Scalar_Bound_Observation
  imports LP_Prolog_Binary64_Encoding
begin

text \<open>This is an observation of an actual scalar, not an evaluation rule.
It does not make arbitrary ground terms numeric. Successful evaluation and
comparison must establish this observation before its bounds can constrain a
residual. The observation is unique and stable under source substitution.\<close>

definition lpp_scalar_fraction where
  "lpp_scalar_fraction t n d =
    ((t=lpp_integer_value n \<and> d=1) \<or>
     (\<exists>bits. lpp_binary64_finite bits \<and> t=lpp_binary64_value bits \<and>
       lpp_binary64_fraction bits=(n,d)))"

lemma lpp_scalar_fraction_unique:
  assumes first: "lpp_scalar_fraction t n d" and second: "lpp_scalar_fraction t m e"
  shows "(n,d)=(m,e)"
proof -
  have injective: "lpp_binary64_finite a \<Longrightarrow> lpp_binary64_finite b \<Longrightarrow>
    lpp_binary64_value a=lpp_binary64_value b \<Longrightarrow> a=b" for a b
    by (rule lpp_binary64_value_injective) (auto simp: lpp_binary64_finite_def)
  show ?thesis using first second
    by (auto simp: lpp_scalar_fraction_def lpp_binary64_not_integer
      lpp_binary64_not_integer[symmetric] dest: injective)
qed

lemma lpp_scalar_fraction_denominator:
  "lpp_scalar_fraction t n d \<Longrightarrow> 0<d"
  by (auto simp: lpp_scalar_fraction_def; metis lpp_binary64_denominator_positive snd_conv)

lemma lpp_scalar_fraction_ground:
  "lpp_scalar_fraction t n d \<Longrightarrow> lp_seg_ground t"
  by (auto simp: lpp_scalar_fraction_def lpp_integer_value_def
    intro: lpp_binary64_value_ground lp_seg_ground.intros)

lemma lpp_scalar_fraction_subst:
  "lpp_scalar_fraction t n d \<Longrightarrow> lpp_scalar_fraction (lp_isubst t sigma) n d"
  by (auto simp: lpp_scalar_fraction_def)

definition lpp_scalar_floor where
  "lpp_scalar_floor t = (THE bound. \<exists>n d. lpp_scalar_fraction t n d \<and> bound=n div d)"

lemma lpp_scalar_floor_exact:
  assumes observed: "lpp_scalar_fraction t n d"
  shows "lpp_scalar_floor t=n div d"
  unfolding lpp_scalar_floor_def
proof (rule the_equality)
  show "\<exists>a b. lpp_scalar_fraction t a b \<and> n div d=a div b" using observed by blast
  fix bound
  assume "\<exists>a b. lpp_scalar_fraction t a b \<and> bound=a div b"
  then show "bound=n div d" using lpp_scalar_fraction_unique[OF observed] by blast
qed

lemma lpp_scalar_bound_transport:
  assumes observed: "lpp_scalar_fraction t n d"
  shows "lpp_scalar_floor (lp_isubst t sigma)=lpp_scalar_floor t"
  using lpp_scalar_floor_exact[OF observed]
    lpp_scalar_floor_exact[OF lpp_scalar_fraction_subst[OF observed]] by simp

lemma lpp_scalar_integer_counter_descent:
  assumes observed: "lpp_scalar_fraction t n d" and bound: "k*d\<le>n"
    and progress: "k<later"
  shows "nat (lpp_scalar_floor t-later+1)<nat (lpp_scalar_floor t-k+1)"
  unfolding lpp_scalar_floor_exact[OF observed]
  by (rule lpp_fraction_bounded_counter_descent[OF lpp_scalar_fraction_denominator[OF observed] bound progress])

ML \<open>
val checked = [@{thm lpp_scalar_fraction_unique}, @{thm lpp_scalar_fraction_denominator},
  @{thm lpp_scalar_fraction_ground}, @{thm lpp_scalar_fraction_subst},
  @{thm lpp_scalar_floor_exact}, @{thm lpp_scalar_bound_transport},
  @{thm lpp_scalar_integer_counter_descent}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted scalar bound dependency" else ();
\<close>
end
