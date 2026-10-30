theory LP_Prolog_Ground_Disequality
  imports LP_Prolog_Integer_Source
begin

definition lpp_disequality_predicate :: string where
  "lpp_disequality_predicate = map char_of_nat [50,58,92,61]"

lemma lpp_disequality_names [simp]:
  "lpp_var_name lpp_disequality_predicate = False"
  "lpp_identity_name lpp_disequality_predicate = False"
  "lpp_source_comparison lpp_disequality_predicate = None"
  "lpp_disequality_predicate \<noteq> ''2:is''"
  "lpp_disequality_predicate \<noteq> ''1:integer''"
  "(lpp_disequality_predicate,2)\<in>lpp_builtin_signature"
  by code_simp+

lemma lpp_disequality_literal_names [simp]:
  "''2:is''\<noteq>lpp_disequality_predicate"
  "''1:integer''\<noteq>lpp_disequality_predicate"
  "''2:<''\<noteq>lpp_disequality_predicate"
  "''2:>''\<noteq>lpp_disequality_predicate"
  "''2:=<''\<noteq>lpp_disequality_predicate"
  "''2:>=''\<noteq>lpp_disequality_predicate"
  "''2:=:=''\<noteq>lpp_disequality_predicate"
  "map char_of_nat [50,58,61,92,61]\<noteq>lpp_disequality_predicate"
  by code_simp+

lemma lpp_disequality_outside_legacy_domain [simp]:
  "lpp_integer_source_domain lpp_disequality_predicate ts = False"
  by (simp only: lpp_integer_source_domain.simps lpp_disequality_names if_False option.case)
    simp

text \<open>For finite ground operands, rational unifiability is equality.
This side condition permits the established disequality branch to use the
existing identity-test outcome, without treating arbitrary rational terms as
finite or assuming that nonground disequality is an identity test.\<close>

lemma lpp_ground_unifiable_iff_equal:
  fixes a b :: "('f,'v) lp_iterm"
  assumes left: "lp_seg_ground a" and right: "lp_seg_ground b"
  shows "(\<exists>sigma :: 'v \<Rightarrow> ('f,'v) lp_iterm. lp_isubst a sigma=lp_isubst b sigma) = (a=b)"
  by (simp add: lp_seg_ground_subst[OF left] lp_seg_ground_subst[OF right])

definition lpp_ground_disequality_outcome where
  "lpp_ground_disequality_outcome a b outcome =
    (lp_seg_ground a \<and> lp_seg_ground b \<and>
      outcome=(if a=b then LPPBuiltinFailure else LPPBuiltinSuccess LPIVar))"

lemma lpp_ground_disequality_exact:
  fixes a b :: "('f,'v) lp_iterm"
  assumes left: "lp_seg_ground a" and right: "lp_seg_ground b"
  shows "lpp_ground_disequality_outcome a b outcome =
    (outcome=(if \<exists>sigma :: 'v \<Rightarrow> ('f,'v) lp_iterm. lp_isubst a sigma=lp_isubst b sigma
      then LPPBuiltinFailure else LPPBuiltinSuccess LPIVar))"
  by (simp add: lpp_ground_disequality_outcome_def left right
    lpp_ground_unifiable_iff_equal[OF left right])

lemma lpp_ground_disequality_total:
  "lp_seg_ground a \<Longrightarrow> lp_seg_ground b \<Longrightarrow>
    \<exists>outcome. lpp_ground_disequality_outcome a b outcome"
  by (auto simp: lpp_ground_disequality_outcome_def)

end
