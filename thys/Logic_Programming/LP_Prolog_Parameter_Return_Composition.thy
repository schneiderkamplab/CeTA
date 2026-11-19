theory LP_Prolog_Parameter_Return_Composition
 imports LP_Prolog_Parameter_Leaf_Budget LP_Prolog_Runtime_Leaf_Invariant
begin

text \<open>A successful counter return either copies the current ground
parameter or returns an evaluated scalar. The relation below records this
structural property without equating groundness with integer typing. Its use
in a source contract still requires proof for every successful return path.\<close>

definition lpp_parameter_return where
 "lpp_parameter_return c d = (d=c \<or> (\<exists>h. d=Fun h []))"

lemma lpp_parameter_return_reflexive:
 "lpp_parameter_return c c"
 by (simp add: lpp_parameter_return_def)

lemma lpp_parameter_return_transitive:
 "lpp_parameter_return c d \<Longrightarrow> lpp_parameter_return d e \<Longrightarrow>
  lpp_parameter_return c e"
 by (auto simp: lpp_parameter_return_def)

lemma lpp_parameter_return_ground:
 "vars_term c={} \<Longrightarrow> lpp_parameter_return c d \<Longrightarrow> vars_term d={}"
 by (auto simp: lpp_parameter_return_def)

lemma lpp_parameter_return_templates:
 "lpp_parameter_return c d \<Longrightarrow>
  lpp_parameter_leaf_templates f g d \<subseteq> lpp_parameter_leaf_templates f g c"
 by (auto simp: lpp_parameter_return_def lpp_parameter_leaf_templates_def)

lemma lpp_leaf_effect_replacements_mono:
 assumes related: "lpp_leaf_effect A s t" and included: "A\<subseteq>B"
 shows "lpp_leaf_effect B s t"
 using related
 by (induct rule: lpp_leaf_effect.induct)
   (auto intro: lpp_leaf_effect.intros dest: subsetD[OF included] elim: list_all2_mono)

lemma lpp_parameter_return_leaf_composition:
 assumes first_effect: "lpp_leaf_effect (lpp_parameter_leaf_templates f g c) s t"
 and returned: "lpp_parameter_return c d"
 and second_effect: "lpp_leaf_effect (lpp_parameter_leaf_templates f g d) t u"
 and ground: "vars_term c={}"
 shows "lpp_leaf_effect (lpp_parameter_leaf_templates f g c) s u"
proof -
 have widened: "lpp_leaf_effect (lpp_parameter_leaf_templates f g c) t u"
  by (rule lpp_leaf_effect_replacements_mono[OF second_effect
    lpp_parameter_return_templates[OF returned]])
 show ?thesis by (rule lpp_leaf_effect_transitive[OF first_effect widened])
   (rule lpp_parameter_leaf_templates_ground[OF ground])
qed

lemma lpp_parameter_return_runtime_effect:
 assumes effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g d) s runtime_value"
 and returned: "lpp_parameter_return c d"
 shows "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g c) s runtime_value"
 using effect lpp_leaf_effect_replacements_mono[OF _ lpp_parameter_return_templates[OF returned]]
 unfolding lpp_runtime_leaf_effect_def by blast

lemma lpp_stable_is_parameter_return:
 assumes success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu)"
 shows "\<exists>d. lp_isubst a mu=lp_ieval d LPIVar \<and> lpp_parameter_return c d"
proof -
 obtain h where chosen: "lpp_scalar_unifier a h=Some mu"
  using success by (auto simp: lpp_stable_is_outcome_def split: option.splits)
 show ?thesis by (rule exI[of _ "Fun (LPCUser h) []"])
  (simp add: lpp_scalar_unifier_sound[OF chosen] lpp_parameter_return_def)
qed

lemma lpp_ground_return_does_not_imply_parameter_return:
 "vars_term (Fun (2::nat) [Fun 3 []] :: (nat,unit) term)={} \<and>
  \<not>lpp_parameter_return (Fun 4 []) (Fun 2 [Fun 3 []])"
 by (simp add: lpp_parameter_return_def)

ML \<open>
val checked = @{thms lpp_parameter_return_reflexive lpp_parameter_return_transitive
 lpp_parameter_return_ground lpp_parameter_return_templates lpp_leaf_effect_replacements_mono
 lpp_parameter_return_leaf_composition lpp_parameter_return_runtime_effect
 lpp_stable_is_parameter_return lpp_ground_return_does_not_imply_parameter_return};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter return composition" else ();
\<close>
end
