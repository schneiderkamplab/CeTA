theory LP_Prolog_Separation_Context
 imports LP_Prolog_Finite_Fresh_Body LP_Prolog_Functor_Context
begin

text \<open>Runtime support separation is distinct from freeness. It is not
preserved by arbitrary substitutions. Transport checks must bind the actual
interface terms; acquisition below uses the actual fresh-clause resolution.\<close>

datatype 'v lpp_separation_fact = LPPSeparate
 "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"

fun lpp_separation_holds where
 "lpp_separation_holds eta (LPPSeparate a b) =
  (set2_lp_iterm (lp_ieval a eta) \<inter> set2_lp_iterm (lp_ieval b eta) = {})"

fun lpp_separation_subst where
 "lpp_separation_subst (LPPSeparate a b) mu = LPPSeparate (a\<cdot>mu) (b\<cdot>mu)"

lemma lpp_separation_subst_eval:
 "lpp_separation_holds eta (lpp_separation_subst observation mu) =
  lpp_separation_holds (\<lambda>x. lp_ieval (mu x) eta) observation"
 by (cases observation) (simp add: lp_ieval_finite_subst)

definition lpp_check_separation_transport where
 "lpp_check_separation_transport before after bindings =
  list_all (\<lambda>observation. lpp_separation_subst observation bindings\<in>set before) after"

lemma lpp_check_separation_transport_sound:
 assumes checked: "lpp_check_separation_transport before after bindings"
 and known: "list_all (lpp_separation_holds eta) before"
 shows "list_all (lpp_separation_holds (\<lambda>x. lp_ieval (bindings x) eta)) after"
 using checked known
 by (auto simp: lpp_check_separation_transport_def list_all_iff lpp_separation_subst_eval[symmetric])

lemma lpp_fresh_univ_acquires_separation:
 assumes checked: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 shows "list_all (lpp_separation_holds rho)
  [LPPSeparate (Var x) (Var y),LPPSeparate (Var x) (Var z)]"
 using lpp_check_fresh_univ_clause_sound[OF checked mgu finite]
 by auto

lemma lpp_separated_univ_finite_goals:
 assumes outcome: "lpp_univ_decompose_outcome names (LPIFun f ts)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [eta y,eta z]) (LPPBuiltinSuccess mu)"
 and input: "lp_ieval t eta=LPIFun f ts"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "y\<noteq>z"
 and free: "lpc_free_knowledge {y,z} eta"
 and separated: "list_all (lpp_separation_holds eta)
   [LPPSeparate t (Var y),LPPSeparate t (Var z)]"
 and goals: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>u. lp_isubst u mu)) gs)"
proof -
 obtain n r where images: "eta y=LPIVar n" "eta z=LPIVar r"
   using free by (auto simp: lpc_free_knowledge_def)
 have unequal: "n\<noteq>r"
   using free distinct images by (auto simp: lpc_free_knowledge_def inj_on_def)
 have fresh: "n\<notin>set2_lp_iterm (LPIFun f ts)" "r\<notin>set2_lp_iterm (LPIFun f ts)"
   using separated input images by auto
 show ?thesis
   by (rule lpp_fresh_univ_finite_goals[OF _ finite unequal fresh goals])
     (use outcome images in simp)
qed

lemma lpp_separation_missing_fact_rejected:
 "\<not> lpp_check_separation_transport [] [observation] bindings"
 by (simp add: lpp_check_separation_transport_def)

lemma lpp_separation_not_arbitrary_substitution_stable:
 fixes x y :: string
 assumes distinct: "x\<noteq>y"
 shows "lpp_separation_holds LPIVar (LPPSeparate (Var x) (Var y)) \<and>
  \<not>lpp_separation_holds (LPIVar(x := LPIVar y)) (LPPSeparate (Var x) (Var y))"
 using distinct by simp

lemma lpp_free_outputs_do_not_imply_separation:
 fixes x y z :: string
 assumes distinct: "y\<noteq>z" "x\<noteq>y" "x\<noteq>z"
 defines "eta \<equiv> LPIVar(x := LPIFun (LPCUser ''cell'') [LPIVar z])"
 shows "lpc_free_knowledge {y,z} eta \<and> lpp_finite_term (eta x) \<and>
  \<not>lpp_separation_holds eta (LPPSeparate (Var x) (Var z))"
 using distinct by (auto simp: eta_def lpc_free_knowledge_def inj_on_def)

ML \<open>
val checked = @{thms lpp_separated_univ_finite_goals lpp_check_separation_transport_sound lpp_fresh_univ_acquires_separation
 lpp_separation_missing_fact_rejected lpp_separation_not_arbitrary_substitution_stable
 lpp_free_outputs_do_not_imply_separation};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted support separation" else ();
\<close>
end
