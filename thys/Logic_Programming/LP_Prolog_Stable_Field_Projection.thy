theory LP_Prolog_Stable_Field_Projection
 imports LP_Prolog_Observed_Equation_Rewrite
begin

text \<open>Observe fixed finite paths through constructors, including rational
values. Definedness is checked at every endpoint. No field_path length is used as a
termination measure and no cyclic value is assumed finite.\<close>

fun lpp_term_field :: "nat list \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term option" where
  "lpp_term_field [] t = Some t"
| "lpp_term_field (i#field_path) (Var x) = None"
| "lpp_term_field (i#field_path) (Fun f ts) =
    (if i<length ts then lpp_term_field field_path (ts!i) else None)"

fun lpp_value_field :: "nat list \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> ('f,'v) lp_iterm option" where
  "lpp_value_field [] t = Some t"
| "lpp_value_field (i#field_path) (LPIVar x) = None"
| "lpp_value_field (i#field_path) (LPIFun f ts) =
    (if i<length ts then lpp_value_field field_path (ts!i) else None)"

lemma lpp_term_field_eval:
  assumes "lpp_term_field field_path t=Some u"
  shows "lpp_value_field field_path (lp_ieval t eta)=Some (lp_ieval u eta)"
  using assms
proof (induct field_path arbitrary: t)
  case Nil then show ?case by simp
next
  case (Cons i field_path)
  then show ?case by (cases t) (auto split: if_splits)
qed

lemma lpp_value_field_subst:
  assumes "lpp_value_field field_path t=Some u"
  shows "lpp_value_field field_path (lp_isubst t sigma)=Some (lp_isubst u sigma)"
  using assms
proof (induct field_path arbitrary: t)
  case Nil then show ?case by simp
next
  case (Cons i field_path)
  then show ?case by (cases t) (auto split: if_splits)
qed

definition lpp_field_call_valid where
  "lpp_field_call_valid field_plan choose_field a = list_all (\<lambda>(i,field_path).
    i<length (snd a) \<and> choose_field field_path (snd a!i)\<noteq>None) (field_plan (fst a))"

definition lpp_field_call where
  "lpp_field_call field_plan choose_field a = (fst a,
    map (\<lambda>(i,field_path). the (choose_field field_path (snd a!i))) (field_plan (fst a)))"

lemma lpp_field_call_eval_valid:
  assumes valid: "lpp_field_call_valid field_plan lpp_term_field a"
  shows "lpp_field_call_valid field_plan lpp_value_field (lpp_success_atom_eval a eta)"
proof -
  have field: "lpp_value_field field_path (lp_ieval (snd a!i) eta)\<noteq>None"
    if member: "(i,field_path)\<in>set (field_plan (fst a))" for i field_path
  proof -
    obtain t where "lpp_term_field field_path (snd a!i)=Some t"
      using valid member by (auto simp: lpp_field_call_valid_def list_all_iff split: option.splits)
    then show ?thesis using lpp_term_field_eval by fastforce
  qed
  show ?thesis using valid field
    by (auto simp: lpp_field_call_valid_def lpp_success_atom_eval_def list_all_iff)
qed

lemma lpp_field_call_eval:
  assumes valid: "lpp_field_call_valid field_plan lpp_term_field a"
  shows "lpp_success_atom_eval (lpp_field_call field_plan lpp_term_field a) eta =
    lpp_field_call field_plan lpp_value_field (lpp_success_atom_eval a eta)"
proof -
  have field: "lp_ieval (the (lpp_term_field field_path (snd a!i))) eta =
      the (lpp_value_field field_path (map (\<lambda>t. lp_ieval t eta) (snd a)!i))"
    if member: "(i,field_path)\<in>set (field_plan (fst a))" for i field_path
  proof -
    obtain t where defined: "lpp_term_field field_path (snd a!i)=Some t" and index: "i<length (snd a)"
      using valid member by (auto simp: lpp_field_call_valid_def list_all_iff split: option.splits)
    show ?thesis using lpp_term_field_eval[OF defined, of eta] by (simp add: defined index)
  qed
  show ?thesis unfolding lpp_field_call_def lpp_success_atom_eval_def
    by (auto simp: map_map split_def intro!: map_cong field)
qed

lemma lpp_field_call_subst:
  assumes valid: "lpp_field_call_valid field_plan lpp_value_field a"
  shows "lpp_success_iatom_subst (lpp_field_call field_plan lpp_value_field a) sigma =
    lpp_field_call field_plan lpp_value_field (lpp_success_iatom_subst a sigma)"
proof -
  have field: "lp_isubst (the (lpp_value_field field_path (snd a!i))) sigma =
      the (lpp_value_field field_path (map (\<lambda>t. lp_isubst t sigma) (snd a)!i))"
    if member: "(i,field_path)\<in>set (field_plan (fst a))" for i field_path
  proof -
    obtain t where defined: "lpp_value_field field_path (snd a!i)=Some t" and index: "i<length (snd a)"
      using valid member by (auto simp: lpp_field_call_valid_def list_all_iff split: option.splits)
    show ?thesis using lpp_value_field_subst[OF defined, of sigma] by (simp add: defined index)
  qed
  show ?thesis unfolding lpp_field_call_def lpp_success_iatom_subst_def
    by (auto simp: map_map split_def intro!: map_cong field)
qed


fun lpp_field_observed_triple where
  "lpp_field_observed_triple field_plan ((h,ps,b,gs),os) =
    ((lpp_field_call field_plan lpp_term_field h,ps,
      lpp_field_call field_plan lpp_term_field b,gs),os)"

definition lpp_check_field_projection where
  "lpp_check_field_projection field_plan D = list_all (\<lambda>((h,ps,b,gs),os).
    lpp_field_call_valid field_plan lpp_term_field h \<and>
    lpp_field_call_valid field_plan lpp_term_field b) D"

lemma lpp_field_observed_target_valid:
  assumes checked: "lpp_check_field_projection field_plan D"
    and edge: "(a,b)\<in>lpp_stable_observed_calls operation (set D) P"
  shows "lpp_field_call_valid field_plan lpp_value_field b"
proof -
  obtain h ps target gs os eta where member: "((h,ps,target,gs),os)\<in>set D"
    and target: "b=lpp_success_atom_eval target eta"
    using edge by (auto simp: lpp_stable_observed_calls_def)
  have valid: "lpp_field_call_valid field_plan lpp_term_field target"
    using checked member by (auto simp: lpp_check_field_projection_def list_all_iff)
  show ?thesis unfolding target by (rule lpp_field_call_eval_valid[OF valid])
qed

lemma lpp_field_observed_call_projection:
  assumes checked: "lpp_check_field_projection field_plan D"
    and edge: "(a,b)\<in>lpp_stable_observed_calls operation (set D) P"
    and valid: "lpp_field_call_valid field_plan lpp_value_field a"
  shows "(lpp_field_call field_plan lpp_value_field a,lpp_field_call field_plan lpp_value_field b)\<in>
    lpp_stable_observed_calls operation (set (map (lpp_field_observed_triple field_plan) D)) P"
proof -
  obtain h ps target gs os sigma eta where
    member: "((h,ps,target,gs),os)\<in>set D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
    and facts: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "b=lpp_success_atom_eval target eta"
    using edge by (auto simp: lpp_stable_observed_calls_def)
  have hv: "lpp_field_call_valid field_plan lpp_term_field h"
    and bv: "lpp_field_call_valid field_plan lpp_term_field target"
    using checked member by (auto simp: lpp_check_field_projection_def list_all_iff)
  have projected: "((lpp_field_call field_plan lpp_term_field h,ps,
      lpp_field_call field_plan lpp_term_field target,gs),os)
      \<in>set (map (lpp_field_observed_triple field_plan) D)"
    using imageI[OF member, of "lpp_field_observed_triple field_plan"] by simp
  have match: "lpp_success_iatom_subst (lpp_field_call field_plan lpp_value_field a) sigma =
      lpp_success_atom_eval (lpp_field_call field_plan lpp_term_field h) eta"
    by (simp only: lpp_field_call_subst[OF valid] matching lpp_field_call_eval[OF hv])
  show ?thesis unfolding lpp_stable_observed_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ "lpp_field_call field_plan lpp_value_field a"],
      rule exI[of _ "lpp_field_call field_plan lpp_term_field h"],
      rule exI[of _ ps], rule exI[of _ "lpp_field_call field_plan lpp_term_field target"],
      rule exI[of _ gs], rule exI[of _ os], rule exI[of _ sigma], rule exI[of _ eta])
    using projected match guards observations facts target
    by (simp add: lpp_field_call_eval[OF bv])
qed

theorem lpp_checked_field_projection_SN:
  assumes checked: "lpp_check_field_projection field_plan D"
    and sn: "SN (lpp_stable_observed_calls operation
      (set (map (lpp_field_observed_triple field_plan) D)) P :: 'w lpp_success_iatom rel)"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: 'w lpp_success_iatom rel)"
  by (rule lpp_typed_successor_simulation_SN[where
      T="lpp_field_call_valid field_plan lpp_value_field" and
      project="lpp_field_call field_plan lpp_value_field", OF sn])
    (meson lpp_field_observed_target_valid[OF checked],
     meson lpp_field_observed_call_projection[OF checked])

ML \<open>
val checked = [@{thm lpp_checked_field_projection_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted finite field projection dependency" else ();
\<close>
end
