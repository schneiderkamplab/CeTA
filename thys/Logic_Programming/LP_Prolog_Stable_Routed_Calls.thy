theory LP_Prolog_Stable_Routed_Calls
 imports LP_Prolog_Stable_Numeric_Component
begin

text \<open>Backend routing partitions the same observed call relation. Cross-component
calls strictly decrease a natural route_rank; every same-route_rank call remains in its
component obligation. This rule does not discharge successful-return contracts.\<close>

lemma lpp_ranked_relation_SN:
  fixes route_rank :: "'a \<Rightarrow> nat"
  assumes weak: "\<And>a b. (a,b)\<in>R \<Longrightarrow> route_rank b\<le>route_rank a"
    and components: "\<And>n. SN {(a,b)\<in>R. route_rank a=n \<and> route_rank b=n}"
  shows "SN R"
proof -
  have point: "\<forall>a. route_rank a=n \<longrightarrow> SN_on R {a}" for n
  proof (induct n rule: less_induct)
    case (less n)
    have local: "route_rank a=n \<longrightarrow> SN_on R {a}" for a
    proof (rule SN_on_induct[OF components[of n] UNIV_I], intro impI)
      fix x
      assume ih: "\<And>y. (x,y)\<in>{(a,b)\<in>R. route_rank a=n \<and> route_rank b=n} \<Longrightarrow>
        route_rank y=n \<longrightarrow> SN_on R {y}"
        and level: "route_rank x=n"
      show "SN_on R {x}"
      proof (rule step_reflects_SN_on)
        fix y assume edge: "(x,y)\<in>R"
        have le: "route_rank y\<le>n" using weak[OF edge] level by simp
        show "SN_on R {y}"
        proof (cases "route_rank y=n")
          case True
          show ?thesis using ih edge level True by auto
        next
          case False
          have "route_rank y<n" using le False by arith
          then show ?thesis using less.hyps by blast
        qed
      qed
    qed
    show ?case using local by blast
  qed
  show ?thesis using point by (auto simp: SN_on_def)
qed

lemma lpp_stable_call_guarded:
  "(a,b)\<in>lpp_stable_observed_calls operation D P \<Longrightarrow>
    (a,b)\<in>lpp_guarded_calls (fst ` D) P (lpp_stable_scalar_evaluation operation)"
proof -
  assume step: "(a,b)\<in>lpp_stable_observed_calls operation D P"
  obtain h ps c gs os sigma eta where member: "((h,ps,c,gs),os)\<in>D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and models: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation)) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and endpoint: "b=lpp_success_atom_eval c eta"
    using step by (auto simp: lpp_stable_observed_calls_def)
  have projected: "(h,ps,c,gs)\<in>fst ` D" using member by force
  show ?thesis unfolding lpp_guarded_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ ps], rule exI[of _ c],
      rule exI[of _ gs], rule exI[of _ sigma], rule exI[of _ eta])
    using projected matching guards models endpoint
    by (auto simp: lpp_success_iatom_subst_def)
qed

lemma lpp_stable_call_structural:
  fixes D :: "'v lpp_observed_triple set" and P :: "'v lpp_success_clause list"
  shows "(a,b)\<in>lpp_stable_observed_calls operation D P \<Longrightarrow>
    (lpp_lift_iatom a,lpp_lift_iatom b)\<in>
      lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P)"
proof -
  assume edge: "(a,b)\<in>lpp_stable_observed_calls operation D P"
  have guarded: "(a,b)\<in>lpp_guarded_calls (fst ` D) P (lpp_stable_scalar_evaluation operation)"
    by (rule lpp_stable_call_guarded[OF edge])
  show ?thesis by (rule lpp_guarded_call_erases[OF guarded])
qed

theorem lpp_stable_structural_component_SN:
  fixes D :: "'v lpp_observed_triple set" and P :: "'v lpp_success_clause list"
  assumes sn: "SN (lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P) ::
      (string lp_cut_symbol,'w) lp_iatom rel)"
  shows "SN (lpp_stable_observed_calls operation D P :: 'w lpp_success_iatom rel)"
  by (rule lpp_typed_successor_simulation_SN[where T="\<lambda>_. True" and project=lpp_lift_iatom, OF sn])
    (auto intro: lpp_stable_call_structural)

definition lpp_stable_rank_rows :: "(string \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'v lpp_observed_triple set \<Rightarrow> 'v lpp_observed_triple set" where
  "lpp_stable_rank_rows route_rank n D = {row\<in>D. case row of ((h,ps,b,gs),os) \<Rightarrow> route_rank (fst h)=n \<and> route_rank (fst b)=n}"

definition lpp_check_stable_routing :: "(string \<Rightarrow> nat) \<Rightarrow> 'v lpp_observed_triple list \<Rightarrow> bool" where
  "lpp_check_stable_routing route_rank D =
    list_all (\<lambda>((h,ps,b,gs),os). route_rank (fst b)\<le>route_rank (fst h)) D"

lemma lpp_stable_call_rank:
  assumes checked: "lpp_check_stable_routing route_rank D"
    and edge: "(a,b)\<in>lpp_stable_observed_calls operation (set D) P"
  shows "route_rank (fst b)\<le>route_rank (fst a)"
  using checked edge
  by (auto simp: lpp_check_stable_routing_def list_all_iff lpp_stable_observed_calls_def
    lpp_success_iatom_subst_def lpp_success_atom_eval_def)

lemma lpp_stable_same_rank_call:
  assumes edge: "(a,b)\<in>lpp_stable_observed_calls operation D P"
    and same: "route_rank (fst a)=n" "route_rank (fst b)=n"
  shows "(a,b)\<in>lpp_stable_observed_calls operation (lpp_stable_rank_rows route_rank n D) P"
proof -
  obtain h ps target gs os sigma eta where row: "((h,ps,target,gs),os)\<in>D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
    and facts: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "b=lpp_success_atom_eval target eta"
    using edge by (auto simp: lpp_stable_observed_calls_def)
  have names: "fst a=fst h" "fst b=fst target"
    using arg_cong[OF matching, of fst] target
    by (auto simp: lpp_success_iatom_subst_def lpp_success_atom_eval_def)
  have member: "((h,ps,target,gs),os)\<in>lpp_stable_rank_rows route_rank n D"
    using row same names by (simp add: lpp_stable_rank_rows_def)
  show ?thesis unfolding lpp_stable_observed_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ ps], rule exI[of _ target],
      rule exI[of _ gs], rule exI[of _ os], rule exI[of _ sigma], rule exI[of _ eta])
    using member matching guards observations facts target by simp
qed

theorem lpp_stable_routed_calls_SN:
  assumes checked: "lpp_check_stable_routing route_rank D"
    and components: "\<And>n. SN (lpp_stable_observed_calls operation (lpp_stable_rank_rows route_rank n (set D)) P ::
      'w lpp_success_iatom rel)"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: 'w lpp_success_iatom rel)"
proof (rule lpp_ranked_relation_SN[where route_rank="route_rank o fst"])
  fix a b assume edge: "(a,b)\<in>lpp_stable_observed_calls operation (set D) P"
  show "(route_rank o fst) b\<le>(route_rank o fst) a" using lpp_stable_call_rank[OF checked edge] by simp
next
  fix n
  show "SN {(a,b)\<in>lpp_stable_observed_calls operation (set D) P.
    (route_rank o fst) a=n \<and> (route_rank o fst) b=n}"
    by (rule SN_subset[OF components[of n]]) (auto intro: lpp_stable_same_rank_call)
qed

ML \<open>
val checked = [@{thm lpp_ranked_relation_SN}, @{thm lpp_stable_structural_component_SN},
  @{thm lpp_stable_routed_calls_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable routing dependency" else ();
\<close>
end
