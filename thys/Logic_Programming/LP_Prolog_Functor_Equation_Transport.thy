theory LP_Prolog_Functor_Equation_Transport
 imports LP_Prolog_Functor_Context LP_Source_Tree
begin

definition lpp_functor_equation_match where
 "lpp_functor_equation_match fuel eqs a b =
   (a=b \<or> (case lp_normalize_goals fuel eqs
      [((),lpp_functor_fact_terms a),((),lpp_functor_fact_terms b)] of
      Some (Some [(_,xs),(_,ys)]) \<Rightarrow> xs=ys | _ \<Rightarrow> False))"

lemma lpp_functor_equation_match_sound:
 assumes checked: "lpp_functor_equation_match fuel eqs a b"
 and equations: "lp_equations eqs eta"
 shows "lpp_functor_fact_holds names eta a = lpp_functor_fact_holds names eta b"
proof (cases "a=b")
 case True then show ?thesis by simp
next
 case False
 obtain result where norm: "lp_normalize_goals fuel eqs
   [((),lpp_functor_fact_terms a),((),lpp_functor_fact_terms b)] = Some (Some result)"
   and matched: "(case result of [(_,xs),(_,ys)] \<Rightarrow> xs=ys | _ \<Rightarrow> False)"
   using checked False unfolding lpp_functor_equation_match_def
   by (auto split: option.splits)
 obtain front rest where r: "result=front#rest" using matched by (cases result) auto
 obtain second_item tail_results where rr: "rest=second_item#tail_results" using matched r by (cases rest) (auto split: prod.splits)
 have tail_results: "tail_results=[]" using matched r rr by (cases tail_results) (auto split: prod.splits)
 obtain xs ys where shape: "result=[((),xs),((),ys)]" using r rr tail_results by (cases front; cases second_item) auto
 have normalized: "lp_normalize_goals fuel eqs
   [((),lpp_functor_fact_terms a),((),lpp_functor_fact_terms b)] = Some (Some [((),xs),((),ys)])"
   using norm shape by simp
 have same: "xs=ys" using matched shape by simp
 have evaluated_terms: "map (\<lambda>t. lp_ieval t eta) (lpp_functor_fact_terms a) =
   map (\<lambda>t. lp_ieval t eta) (lpp_functor_fact_terms b)"
   using lp_normalize_goals_sound[OF normalized equations] same
   by (auto simp: lp_atom_eval_def)
 show ?thesis using evaluated_terms by (cases a; cases b) auto
qed

definition lpp_check_functor_equation_transport where
 "lpp_check_functor_equation_transport fuel eqs source_facts target_facts bindings =
   list_all (\<lambda>b. list_ex (\<lambda>a. lpp_functor_equation_match fuel eqs a
      (lpp_functor_fact_subst b bindings)) source_facts) target_facts"

lemma lpp_check_functor_equation_transport_sound:
 assumes checked: "lpp_check_functor_equation_transport fuel eqs source_facts target_facts bindings"
 and equations: "lp_equations eqs eta"
 and held: "list_all (lpp_functor_fact_holds names eta) source_facts"
 shows "list_all (lpp_functor_fact_holds names (\<lambda>x. lp_ieval (bindings x) eta)) target_facts"
proof (unfold list_all_iff, intro ballI)
 fix b assume member: "b\<in>set target_facts"
 obtain a where source: "a\<in>set source_facts"
   and matches: "lpp_functor_equation_match fuel eqs a (lpp_functor_fact_subst b bindings)"
   using checked member by (auto simp: lpp_check_functor_equation_transport_def list_all_iff list_ex_iff)
 have "lpp_functor_fact_holds names eta a" using held source by (simp add: list_all_iff)
 then show "lpp_functor_fact_holds names (\<lambda>x. lp_ieval (bindings x) eta) b"
   using lpp_functor_equation_match_sound[OF matches equations]
   by (simp add: lpp_functor_fact_subst_eval)
qed

lemma lpp_functor_equation_match_empty[simp]:
 "lpp_functor_equation_match fuel [] a b = (a=b)"
 by (cases fuel; cases a; cases b) (simp_all add: lpp_functor_equation_match_def)

lemma lpp_functor_equation_transport_empty[simp]:
 "lpp_check_functor_equation_transport fuel [] source_facts target_facts bindings =
   lpp_check_functor_transport source_facts target_facts bindings"
 by (auto simp: lpp_check_functor_equation_transport_def lpp_check_functor_transport_def list_ex_iff)

ML \<open>
val checked = @{thms lpp_functor_equation_match_sound lpp_check_functor_equation_transport_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted equation-aware functor transport" else ();
\<close>
end
