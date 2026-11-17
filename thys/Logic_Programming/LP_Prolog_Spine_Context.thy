theory LP_Prolog_Spine_Context
 imports LP_Prolog_Functor_Spine_Return LP_Prolog_Finite_List_Head
begin

text \<open>Proper-spine observations are frame-local template facts. They do
not assert finite elements. Checked derivations acquire argument spines from
functor observations or expose a known cons tail; interface transport is exact
one-pass substitution. Actual-return preservation requires initialization in
every incoming frame, including saved alternatives.\<close>

definition lpp_spine_holds where
 "lpp_spine_holds eta t = (\<exists>n. lpp_list_length (lp_ieval t eta) n)"

datatype lpp_spine_rule = LPPSpineExisting nat | LPPSpineArguments nat
 | LPPSpineTail nat | LPPSpineNil | LPPSpineCons nat

fun lpp_check_spine_rule where
 "lpp_check_spine_rule facts spines t (LPPSpineExisting i) =
   (i<length spines \<and> spines!i=t)"
| "lpp_check_spine_rule facts spines t (LPPSpineArguments i) =
   (i<length facts \<and> (case facts!i of LPPFunctorFact value_term name_term arglist \<Rightarrow> arglist=t))"
| "lpp_check_spine_rule facts spines t (LPPSpineTail i) =
   (i<length spines \<and> (case spines!i of
     Fun f [h,tail_term] \<Rightarrow> f=LPCUser ''2:prolog_data_2e'' \<and> tail_term=t | _ \<Rightarrow> False))"
| "lpp_check_spine_rule facts spines t LPPSpineNil =
   (t=Fun (LPCUser ''0:prolog_data_5b5d'') [])"
| "lpp_check_spine_rule facts spines t (LPPSpineCons i) =
   (i<length spines \<and> (case t of
     Fun f [h,tail_term] \<Rightarrow> f=LPCUser ''2:prolog_data_2e'' \<and> tail_term=spines!i | _ \<Rightarrow> False))"

lemma lpp_spine_holds_subst:
 "lpp_spine_holds eta (t\<cdot>mu) = lpp_spine_holds (\<lambda>x. lp_ieval (mu x) eta) t"
 by (simp add: lpp_spine_holds_def lp_ieval_finite_subst)

lemma lpp_spine_holds_runtime_subst:
 "lpp_spine_holds eta t \<Longrightarrow> lpp_spine_holds (\<lambda>x. lp_isubst (eta x) sigma) t"
 by (auto simp: lpp_spine_holds_def lp_ieval_subst[symmetric] intro: lpp_list_length_subst)

lemma lpp_functor_argument_spine:
 assumes fact: "lpp_functor_fact_holds names eta (LPPFunctorFact value_term name_term arglist)"
 shows "lpp_spine_holds eta arglist"
 using fact lpp_constructor_arguments_spine
 by (auto simp: lpp_spine_holds_def lpp_functor_observation_def)

lemma lpp_spine_tail:
 "lpp_spine_holds eta (Fun (LPCUser ''2:prolog_data_2e'') [h,t]) \<Longrightarrow> lpp_spine_holds eta t"
 unfolding lpp_spine_holds_def by (auto elim: lpp_list_length.cases)

lemma lpp_spine_cons:
 "lpp_spine_holds eta t \<Longrightarrow> lpp_spine_holds eta (Fun (LPCUser ''2:prolog_data_2e'') [h,t])"
 unfolding lpp_spine_holds_def by (auto intro: lpp_list_length.intros)

lemma lpp_check_spine_rule_sound:
 assumes checked: "lpp_check_spine_rule facts spines t derivation"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and spines: "list_all (lpp_spine_holds eta) spines"
 shows "lpp_spine_holds eta t"
proof -
 have known: "lpp_spine_holds eta (spines!i)" if "i<length spines" for i
   using spines that by (simp add: list_all_length)
 have observed: "lpp_functor_fact_holds names eta (facts!i)" if "i<length facts" for i
   using facts that by (simp add: list_all_length)
 have nil: "lpp_spine_holds eta (Fun (LPCUser ''0:prolog_data_5b5d'') [])"
   unfolding lpp_spine_holds_def by (auto intro: exI[of _ 0] lpp_list_length.intros)
 show ?thesis
 proof (cases derivation)
  case (LPPSpineExisting i)
  then show ?thesis using checked known by auto
 next
  case (LPPSpineArguments i)
  then have bound: "i<length facts" and fields:
   "case facts!i of LPPFunctorFact value_term name_term arglist \<Rightarrow> arglist=t"
    using checked by auto
  obtain value_term name_term where shape: "facts!i=LPPFunctorFact value_term name_term t"
    using fields by (cases "facts!i") auto
  have fact: "lpp_functor_fact_holds names eta (LPPFunctorFact value_term name_term t)"
    using observed[OF bound] by (simp add: shape)
  show ?thesis by (rule lpp_functor_argument_spine[OF fact])
 next
  case (LPPSpineTail i)
  then obtain h where bound: "i<length spines" and shape:
    "spines!i=Fun (LPCUser ''2:prolog_data_2e'') [h,t]"
    using checked by (auto split: term.splits list.splits)
  show ?thesis using lpp_spine_tail known[OF bound] by (auto simp: shape)
 next
  case LPPSpineNil
  then show ?thesis using checked nil by simp
 next
  case (LPPSpineCons i)
  then obtain h where bound: "i<length spines" and shape:
    "t=Fun (LPCUser ''2:prolog_data_2e'') [h,spines!i]"
    using checked by (auto split: term.splits list.splits)
  show ?thesis using lpp_spine_cons[OF known[OF bound], of h] by (simp add: shape)
 qed
qed

definition lpp_check_spine_transport where
 "lpp_check_spine_transport source_spines target_spines bindings =
   list_all (\<lambda>t. t\<cdot>bindings\<in>set source_spines) target_spines"

lemma lpp_check_spine_transport_sound:
 "lpp_check_spine_transport source_spines target_spines bindings \<Longrightarrow>
  list_all (lpp_spine_holds eta) source_spines \<Longrightarrow>
  list_all (lpp_spine_holds (\<lambda>x. lp_ieval (bindings x) eta)) target_spines"
 by (auto simp: lpp_check_spine_transport_def list_all_iff lpp_spine_holds_subst[symmetric])

lemma lpp_actual_return_preserves_spine_context:
 assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and initialized: "list_all (\<lambda>frame. list_all (lpp_spine_holds (snd frame)) spines) ss"
 shows "list_all (lpp_spine_holds eta) spines"
 by (rule lpp_actual_return_substitution_property[where
      F="\<lambda>rho. list_all (lpp_spine_holds rho) spines", OF _ actual initialized])
   (auto simp: list_all_iff intro: lpp_spine_holds_runtime_subst)


lemma lpp_actual_return_spine_interface:
 assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and initialized: "list_all (\<lambda>frame. list_all (lpp_spine_holds (snd frame)) source_spines) ss"
 and checked: "lpp_check_spine_transport source_spines target_spines bindings"
 shows "list_all (lpp_spine_holds (\<lambda>x. lp_ieval (bindings x) eta)) target_spines"
 by (rule lpp_check_spine_transport_sound[OF checked
   lpp_actual_return_preserves_spine_context[OF actual initialized]])

lemma lpp_spine_arguments_missing_rejected:
 "\<not>lpp_check_spine_rule [] spines t (LPPSpineArguments i)"
 by simp

lemma lpp_spine_tail_missing_rejected:
 "\<not>lpp_check_spine_rule facts [] t (LPPSpineTail i)"
 by simp

lemma lpp_missing_spine_transport_rejected:
 "\<not>lpp_check_spine_transport [] [t] bindings"
 by (simp add: lpp_check_spine_transport_def)

ML \<open>
val checked = @{thms lpp_check_spine_rule_sound lpp_check_spine_transport_sound
 lpp_actual_return_preserves_spine_context lpp_actual_return_spine_interface
 lpp_spine_arguments_missing_rejected lpp_spine_tail_missing_rejected
 lpp_missing_spine_transport_rejected};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted spine context" else ();
\<close>
end
