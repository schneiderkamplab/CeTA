theory LP_Prolog_Domain_Guards
 imports LP_Prolog_Domain_Edge
begin

definition lpp_domain_concrete_table where
 "lpp_domain_concrete_table operation domains eta x =
   map_option (\<lambda>d. SOME v. lpp_recurrent_scalar_member d v \<and>
     lpp_stable_scalar_evaluation operation (eta x) (lpp_machine_value v)) (domains x)"

lemma lpp_domain_concrete_member:
 assumes env: "lpp_recurrent_domain_environment operation domains eta"
 and found: "domains x=Some d"
 shows "\<exists>v. lpp_domain_concrete_table operation domains eta x=Some v \<and>
   lpp_recurrent_scalar_member d v \<and>
   lpp_stable_scalar_evaluation operation (eta x) (lpp_machine_value v)"
proof -
 have exists: "\<exists>v. lpp_recurrent_scalar_member d v \<and>
   lpp_stable_scalar_evaluation operation (eta x) (lpp_machine_value v)"
   using env found unfolding lpp_recurrent_domain_environment_def by blast
 show ?thesis using someI_ex[OF exists]
   by (auto simp: lpp_domain_concrete_table_def found)
qed

lemma lpp_domain_concrete_parameters:
 assumes env: "lpp_recurrent_domain_environment operation domains eta"
 and found: "lpp_domain_concrete_table operation domains eta x=Some v"
 shows "lpp_stable_scalar_evaluation operation (eta x) (lpp_machine_value v)"
proof -
 obtain d where entry: "domains x=Some d"
   using found by (auto simp: lpp_domain_concrete_table_def split: option.splits)
 show ?thesis using lpp_domain_concrete_member[OF env entry] found by auto
qed

lemma lpp_domain_template_concrete:
 assumes checked: "lpp_recurrent_template_domain domains e=Some d"
 and concrete: "\<And>x d. domains x=Some d \<Longrightarrow> \<exists>v. table x=Some v \<and> lpp_recurrent_scalar_member d v"
 shows "\<exists>v. lpp_scalar_template_evaluate table e=Some v \<and> lpp_recurrent_scalar_member d v"
 using checked
proof (induct e arbitrary: d)
 case (LPPScalarParameter x)
 show ?case using concrete[OF LPPScalarParameter.prems[simplified]]
   by (auto dest: lpp_recurrent_member_valid)
next
 case (LPPScalarLiteral v) then show ?case by (auto split: if_splits)
next
 case (LPPScalarBinary f a b)
 obtain da db where a: "lpp_recurrent_template_domain domains a=Some da"
 and b: "lpp_recurrent_template_domain domains b=Some db"
 and operated: "lpp_recurrent_scalar_binary f da db=Some d"
 and name: "lpp_scalar_binary_name f"
 using LPPScalarBinary.prems by (auto split: option.splits prod.splits if_splits)
 obtain x where ex: "lpp_scalar_template_evaluate table a=Some x"
 and mx: "lpp_recurrent_scalar_member da x" using LPPScalarBinary.hyps(1)[OF a] by blast
 obtain y where ey: "lpp_scalar_template_evaluate table b=Some y"
 and my: "lpp_recurrent_scalar_member db y" using LPPScalarBinary.hyps(2)[OF b] by blast
 show ?case using lpp_recurrent_scalar_binary_sound[OF operated mx my] ex ey name by simp
qed

fun lpp_domain_guard_total where
 "lpp_domain_guard_total domains (LPPScalarCompare f a b) =
   (lpp_source_comparison f\<noteq>None \<and> lpp_recurrent_template_domain domains a\<noteq>None \<and>
    lpp_recurrent_template_domain domains b\<noteq>None)"
| "lpp_domain_guard_total domains _ = False"

lemma lpp_domain_guard_defined:
 assumes checked: "lpp_domain_guard_total domains g"
 and concrete: "\<And>x d. domains x=Some d \<Longrightarrow> \<exists>v. table x=Some v \<and> lpp_recurrent_scalar_member d v"
 shows "\<exists>held. lpp_scalar_guard_check table g=Some held"
proof (cases g)
 case (LPPScalarCompare f a b)
 obtain da db c reversed where left: "lpp_recurrent_template_domain domains a=Some da"
 and right: "lpp_recurrent_template_domain domains b=Some db"
 and name: "lpp_source_comparison f=Some (c,reversed)"
 using checked by (auto simp only: LPPScalarCompare lpp_domain_guard_total.simps split: option.splits)
 obtain x where ex: "lpp_scalar_template_evaluate table a=Some x"
   using lpp_domain_template_concrete[where domains=domains and table=table and e=a and d=da] left concrete by blast
 obtain y where ey: "lpp_scalar_template_evaluate table b=Some y"
   using lpp_domain_template_concrete[where domains=domains and table=table and e=b and d=db] right concrete by blast
 show ?thesis by (simp only: LPPScalarCompare lpp_scalar_guard_check.simps name ex ey; simp add: Let_def)
next
 case (LPPScalarIsLiteral v e) then show ?thesis using checked by simp
qed

definition lpp_domain_opposite_names where
 "lpp_domain_opposite_names f h =
   ((f=''2:<'' \<and> h=''2:>='') \<or> (f=''2:>='' \<and> h=''2:<'') \<or>
    (f=''2:>'' \<and> h=''2:=<'') \<or> (f=''2:=<'' \<and> h=''2:>'') \<or>
    (f=''2:=:='' \<and> h=map char_of_nat [50,58,61,92,61]) \<or> (f=map char_of_nat [50,58,61,92,61] \<and> h=''2:=:=''))"
fun lpp_domain_opposite_guards where
 "lpp_domain_opposite_guards (LPPScalarCompare f a b) (LPPScalarCompare h c d) =
   (a=c \<and> b=d \<and> lpp_domain_opposite_names f h)"
| "lpp_domain_opposite_guards _ _ = False"

lemma lpp_domain_comparison_codes:
 "lpp_source_comparison ''2:<''=Some (LPPIntLess,False)"
 "lpp_source_comparison ''2:>=''=Some (LPPIntLessEqual,True)"
 "lpp_source_comparison ''2:>''=Some (LPPIntLess,True)"
 "lpp_source_comparison ''2:=<''=Some (LPPIntLessEqual,False)"
 "lpp_source_comparison ''2:=:=''=Some (LPPIntEqual,False)"
 "lpp_source_comparison (map char_of_nat [50,58,61,92,61])=Some (LPPIntNotEqual,False)"
 by code_simp+

lemma lpp_domain_guard_opposite:
 "lpp_domain_opposite_guards g h \<Longrightarrow>
  lpp_scalar_guard_check table h=map_option Not (lpp_scalar_guard_check table g)"
 by (cases g; cases h)
   (auto simp del: lpp_source_comparison.simps simp: lpp_domain_opposite_names_def lpp_domain_comparison_codes[unfolded list.map]
     Let_def split: option.splits prod.splits)

ML \<open>
val checked = [@{thm lpp_domain_template_concrete}, @{thm lpp_domain_guard_defined}, @{thm lpp_domain_guard_opposite}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted domain guard dependency" else ();
\<close>
end
