theory LP_Prolog_Structural_List_Observation
 imports LP_Prolog_Structural_Univ LP_Prolog_Finite_Length
begin

text \<open>A proper spine and finite elements jointly initialize a structural
list observation. Neither premise is supplied by the other. The reverse bridge
recovers the exact spine length, so pointwise effects cannot grow the spine.\<close>

lemma lpp_runtime_structure_constructor:
 "lpp_runtime_structure runtime_value (Fun (Inl f) shapes) \<longleftrightarrow>
 (\<exists>templates. runtime_value=LPIFun f (map (\<lambda>t. lp_ieval t LPIVar) templates) \<and>
   shapes=map lpp_structure_template templates)"
proof
 assume observed: "lpp_runtime_structure runtime_value (Fun (Inl f) shapes)"
 obtain template where value_eq: "runtime_value=lp_ieval template LPIVar"
 and shape: "Fun (Inl f) shapes=lpp_structure_template template"
  using observed unfolding lpp_runtime_structure_def by blast
 show "\<exists>templates. runtime_value=LPIFun f (map (\<lambda>t. lp_ieval t LPIVar) templates) \<and>
   shapes=map lpp_structure_template templates"
  using shape value_eq by (cases template) auto
next
 assume "\<exists>templates. runtime_value=LPIFun f (map (\<lambda>t. lp_ieval t LPIVar) templates) \<and>
   shapes=map lpp_structure_template templates"
 then obtain templates where value_eq: "runtime_value=LPIFun f (map (\<lambda>t. lp_ieval t LPIVar) templates)"
 and shape: "shapes=map lpp_structure_template templates" by blast
 show "lpp_runtime_structure runtime_value (Fun (Inl f) shapes)"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "Fun f templates"]) (simp add: value_eq shape)
qed

lemma lpp_runtime_list_observation_length:
 assumes observed: "lpp_runtime_structure runtime_value (lpp_structural_argument_list xs)"
 shows "lpp_list_length runtime_value (length xs)"
 using observed
proof (induct xs arbitrary: runtime_value)
 case Nil
 then show ?case by (auto simp: lpp_runtime_structure_constructor intro: lpp_list_length.nil)
next
 case (Cons x xs)
 obtain h t where value_eq: "runtime_value=LPIFun (LPCUser ''2:prolog_data_2e'')
   [lp_ieval h LPIVar,lp_ieval t LPIVar]"
 and shape: "lpp_structural_argument_list xs=lpp_structure_template t"
  using Cons.prems by (auto simp: lpp_runtime_structure_constructor map_eq_Cons_conv)
 have tail: "lpp_runtime_structure (lp_ieval t LPIVar) (lpp_structural_argument_list xs)"
  unfolding lpp_runtime_structure_def using shape by blast
 have length: "lpp_list_length (lp_ieval t LPIVar) (length xs)"
  by (rule Cons.hyps[OF tail])
 show ?case unfolding value_eq by (simp add: lpp_list_length.cons[OF length])
qed

lemma lpp_finite_spine_structural_observation:
 assumes spine: "lpp_list_length runtime_value n"
 and finite: "lpp_finite_term runtime_value"
 shows "\<exists>xs. lpp_runtime_structure runtime_value (lpp_structural_argument_list xs) \<and> length xs=n"
 using spine finite
proof (induct rule: lpp_list_length.induct)
 case nil
 show ?case
  by (rule exI[of _ "[]"])
     (auto simp: lpp_runtime_structure_constructor)
next
 case (cons t n h)
 have h_finite: "lpp_finite_term h" and t_finite: "lpp_finite_term t"
  using cons.prems by simp_all
 obtain h_template where h: "h=lp_ieval h_template LPIVar"
  using lpp_finite_runtime_template[OF h_finite] by blast
 obtain xs where observed: "lpp_runtime_structure t (lpp_structural_argument_list xs)"
 and length: "length xs=n" using cons.hyps(2)[OF t_finite] by blast
 obtain t_template where t: "t=lp_ieval t_template LPIVar"
 and shape: "lpp_structural_argument_list xs=lpp_structure_template t_template"
  using observed unfolding lpp_runtime_structure_def by blast
 show ?case
  apply (rule exI[of _ "lpp_structure_template h_template#xs"])
  apply (simp add: lpp_runtime_structure_constructor h t shape length)
  by (rule exI[of _ "[h_template,t_template]"]) simp
qed

lemma lpp_runtime_list_observation_iff:
 "(\<exists>xs. lpp_runtime_structure runtime_value (lpp_structural_argument_list xs) \<and> length xs=n)
  \<longleftrightarrow> lpp_list_length runtime_value n \<and> lpp_finite_term runtime_value"
 using lpp_runtime_list_observation_length lpp_runtime_structure_finite
 lpp_finite_spine_structural_observation by blast

ML \<open>
val checked = @{thms lpp_runtime_structure_constructor lpp_runtime_list_observation_length
 lpp_finite_spine_structural_observation lpp_runtime_list_observation_iff};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted structural list observation" else ();
\<close>
end
