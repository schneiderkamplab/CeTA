theory LP_Prolog_Shape_Refutation
  imports LP_Prolog_Equation_Congruence LP_Prolog_Stable_Contract_Refinement
begin

text \<open>Refutation uses an initialized shape observation and an independently
checked equation rewrite. Fuel exhaustion never establishes a contradiction.
This concerns an incoming context, not termination of the helper producing it.\<close>

definition lpp_check_shape_refutation where
  "lpp_check_shape_refutation fuel context i pattern =
    (i < length (snd (snd context)) \<and>
      (case snd (snd context)!i of LPPOShape G shape t \<Rightarrow>
        lpp_check_context_equation_rewrite context t pattern \<and>
        lp_return_shape_facts fuel G shape pattern = None
      | _ \<Rightarrow> False))"

lemma lpp_shape_refutation_sound:
  assumes checked: "lpp_check_shape_refutation fuel context i pattern"
    and observed: "lpp_evaluation_context_holds E P context eta"
  shows False
proof -
  have bound: "i < length (snd (snd context))"
    using checked by (simp add: lpp_check_shape_refutation_def)
  have selected: "snd (snd context)!i \<in> set (snd (snd context))"
    by (rule nth_mem[OF bound])
  obtain G shape t where constructor: "snd (snd context)!i = LPPOShape G shape t"
    and rewrite: "lpp_check_context_equation_rewrite context t pattern"
    and impossible: "lp_return_shape_facts fuel G shape pattern = None"
    using checked by (auto simp: lpp_check_shape_refutation_def split: lpp_numeric_observation.splits)
  have member: "LPPOShape G shape t \<in> set (snd (snd context))"
    using selected constructor by metis
  have held: "lp_return_shape_holds G shape (lp_ieval t eta)"
    using observed member by (cases "context")
      (auto simp: lpp_evaluation_context_holds_def list_all_iff)
  have equal: "lp_ieval t eta = lp_ieval pattern eta"
    by (rule lpp_context_equation_rewrite_sound[OF rewrite observed])
  have valid: "lp_return_facts_valid G eta (lp_return_shape_facts fuel G shape pattern)"
    by (rule lp_return_shape_facts_sound) (use held equal in auto)
  show False using valid impossible by (simp add: lp_return_facts_valid_def)
qed

lemma lpp_stable_shape_refutation_sound:
  assumes "lpp_check_shape_refutation fuel context i pattern"
    and "lpp_stable_context_holds operation P context eta"
  shows False
  by (rule lpp_shape_refutation_sound[where E="lpp_stable_scalar_evaluation operation" and P=P and eta=eta, OF assms(1)])
    (use assms(2) in \<open>simp add: lpp_stable_context_holds_def\<close>)

lemma lpp_shape_refutation_requires_fuel:
  "\<not> lpp_check_shape_refutation 0 context i pattern"
  by (simp add: lpp_check_shape_refutation_def split: lpp_numeric_observation.splits)

ML \<open>
val checked = [@{thm lpp_shape_refutation_sound}, @{thm lpp_stable_shape_refutation_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted shape refutation dependency" else ();
\<close>
end
