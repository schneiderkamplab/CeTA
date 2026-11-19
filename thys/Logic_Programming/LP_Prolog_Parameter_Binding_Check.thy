theory LP_Prolog_Parameter_Binding_Check
 imports LP_Prolog_Parameter_Return_Composition LP_Cut_MGU_Unify_Free
begin

text \<open>The binding check recognizes parameter copies, atomic values and
marked parameter or atomic values structurally. Symbol names are parameters.
Freeness and the relation to the initial parameter remain authenticated source
facts; this checker does not infer them from a successful residual answer.\<close>

fun lpp_check_parameter_replacement where
 "lpp_check_parameter_replacement parameter f g (Var x) = (x = parameter)"
| "lpp_check_parameter_replacement parameter f g (Fun h []) = True"
| "lpp_check_parameter_replacement parameter f g (Fun h [Fun tag [],Var x]) =
    (h=f \<and> tag=g \<and> x = parameter)"
| "lpp_check_parameter_replacement parameter f g (Fun h [Fun tag [],Fun atom []]) =
    (h=f \<and> tag=g)"
| "lpp_check_parameter_replacement parameter f g _ = False"

fun lpp_check_parameter_binding where
 "lpp_check_parameter_binding F parameter f g (Var x) b =
    (x\<in>set F \<and> lpp_check_parameter_replacement parameter f g b)"
| "lpp_check_parameter_binding F parameter f g _ b = False"

lemma lpp_checked_parameter_replacement_sound:
 assumes checked: "lpp_check_parameter_replacement parameter f g b"
 and parameter: "eta parameter=lp_ieval d LPIVar"
 and returned: "lpp_parameter_return c d"
 shows "\<exists>u\<in>lpp_parameter_leaf_templates f g c. lp_ieval b eta=lp_ieval u LPIVar"
proof -
 have pattern: "b=Var parameter \<or> b=Fun f [Fun g [],Var parameter] \<or>
   (\<exists>h. b=Fun h []) \<or> (\<exists>h. b=Fun f [Fun g [],Fun h []])"
  using checked by (induct parameter f g b rule: lpp_check_parameter_replacement.induct) auto
 have local: "\<exists>u\<in>lpp_parameter_leaf_templates f g d. lp_ieval b eta=lp_ieval u LPIVar"
 proof -
  consider (copy) "b=Var parameter" | (marked) "b=Fun f [Fun g [],Var parameter]"
   | (atom) h where "b=Fun h []" | (marked_atom) h where "b=Fun f [Fun g [],Fun h []]"
   using pattern by blast
  then show ?thesis
  proof cases
   case copy
   show ?thesis by (rule bexI[of _ d]) (simp_all add: copy parameter lpp_parameter_leaf_templates_def)
  next
   case marked
   show ?thesis by (rule bexI[of _ "Fun f [Fun g [],d]"])
    (simp_all add: marked parameter lpp_parameter_leaf_templates_def)
  next
   case (atom h)
   show ?thesis by (rule bexI[of _ "Fun h []"]) (auto simp: atom lpp_parameter_leaf_templates_def)
  next
   case (marked_atom h)
   show ?thesis by (rule bexI[of _ "Fun f [Fun g [],Fun h []]"])
    (auto simp: marked_atom lpp_parameter_leaf_templates_def)
  qed
 qed
 show ?thesis using local lpp_parameter_return_templates[OF returned] by blast
qed

lemma lpp_checked_parameter_binding_sound:
 assumes checked: "lpp_check_parameter_binding F parameter f g a b"
 and free: "lpc_free_knowledge (set F) eta"
 and parameter: "eta parameter=lp_ieval d LPIVar"
 and returned: "lpp_parameter_return c d"
 shows "\<exists>x u. lp_ieval a eta=LPIVar x \<and> lp_ieval b eta=lp_ieval u LPIVar \<and>
   u\<in>lpp_parameter_leaf_templates f g c"
 using checked free lpp_checked_parameter_replacement_sound[where eta=eta and parameter=parameter and b=b and f=f and g=g, OF _ parameter returned]
 by (cases a) (auto simp: lpc_free_knowledge_def)

ML \<open>
val checked = @{thms lpp_checked_parameter_replacement_sound lpp_checked_parameter_binding_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter binding check" else ();
\<close>
end
