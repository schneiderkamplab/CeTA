theory LP_Prolog_Recursive_Entry
 imports LP_Prolog_Cons_Successor_Facts
begin

text \<open>The recursive helper output is fresh; the preserved caller output may
share with the input or tail. Both facts are recorded in the same link valuation.
This is an entry condition, not a recursive answer contract.\<close>

definition lpp_recursive_entry where
 "lpp_recursive_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot eta =
  (lpp_runtime_parameter initial_parameter (eta parameter_slot) \<and>
   lpp_finite_term (eta input_slot) \<and> lpp_finite_term (eta tail_slot) \<and>
   (\<exists>n. lpp_list_length (eta tail_slot) n) \<and>
   (\<exists>u v. eta helper_slot=LPIVar u \<and> eta caller_slot=LPIVar v \<and> u\<noteq>v) \<and>
   set2_lp_iterm (eta helper_slot) \<inter>
    (set2_lp_iterm (eta input_slot) \<union> set2_lp_iterm (eta tail_slot))={})"

definition lpp_check_recursive_entry_coordinates where
 "lpp_check_recursive_entry_coordinates head bs l x y n m fresh_variable
   input_slot parameter_slot helper_slot tail_slot caller_slot bindings =
  (distinct [x,y,n,m] \<and> distinct [input_slot,parameter_slot,helper_slot,tail_slot,caller_slot] \<and>
   lpp_check_clause_coordinate l (Var x) (Var input_slot) bindings \<and>
   lpp_check_clause_coordinate l (Var n) (Var parameter_slot) bindings \<and>
   lpp_check_body_output head bs l fresh_variable (Var helper_slot) bindings \<and>
   lpp_check_clause_coordinate l (Var y) (Var tail_slot) bindings \<and>
   lpp_check_clause_coordinate l (Var m) (Var caller_slot) bindings)"

lemma lpp_checked_recursive_entry:
 fixes k :: nat
 and eta sigma rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_recursive_entry_coordinates
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]) bs l x y n m fresh_variable
   input_slot parameter_slot helper_slot tail_slot caller_slot bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval (Fun p [input_term,Var parameter_variable,Var output_variable]) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
   (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]) bs sigma rho"
 and spine: "lpp_list_length (lp_ieval input_term eta) spine_length"
 and finite_call: "lpp_finite_term (lp_ieval (Fun p [input_term,Var parameter_variable,Var output_variable]) eta)"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_variable)"
 and caller_free: "lpc_free_knowledge {output_variable} eta"
 defines target_env: "nu \<equiv> (\<lambda>v. lp_ieval (lp_cut_instance_subst bindings v) (lp_cut_resolution_env k l eta sigma rho))"
 shows "lpp_recursive_entry initial_parameter input_slot parameter_slot helper_slot tail_slot caller_slot nu"
proof -
 let ?head = "Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var m]"
 let ?call = "Fun p [input_term,Var parameter_variable,Var output_variable]"
 have distinct: "distinct (x#y#[n,m])" using checked by (simp add: lpp_check_recursive_entry_coordinates_def)
 have actual: "lpc_mgu_resolve (LPIFun p (lp_ieval input_term eta#[eta parameter_variable,eta output_variable]))
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) ?head bs sigma rho"
  using mgu by simp
 obtain witness where matching: "lp_ieval ?head witness=lp_ieval ?call eta"
  using lpp_spine_head_matching_witness[where H="[n,m]", unfolded list.map, OF spine actual distinct] by auto
 have coverage: "{output_variable}\<subseteq>vars_term ?call \<union>
   (\<Union>goal\<in>set gs. \<Union>t\<in>set (lp_cut_terms goal). vars_term t)" by simp
 have preserved: "lpc_free_knowledge {output_variable} (\<lambda>v. lp_isubst (eta v) sigma)"
  by (rule lpp_matching_free_outputs[OF mgu matching caller_free coverage])
 have equation: "lp_isubst (lp_ieval ?call eta) sigma=lp_ieval ?head rho"
  using mgu by (simp add: lpc_mgu_resolve_def)
 have output_value: "rho m=lp_isubst (eta output_variable) sigma" using equation by simp
 have parameter_value: "rho n=eta parameter_variable"
  using equation lpp_runtime_parameter_ground[OF tracked] by (simp add: lp_seg_ground_subst)
 have finite_head: "lpp_finite_term (lp_ieval ?head rho)"
  by (rule lpp_matching_head_finite_instance[OF mgu matching finite_call])
 have fresh_map: "lpp_check_body_output ?head bs l fresh_variable (Var helper_slot) bindings"
  using checked by (simp add: lpp_check_recursive_entry_coordinates_def)
 have finite_subst: "lpp_finite_term (lp_isubst (lp_ieval ?call eta) sigma)"
  using finite_head equation by simp
 have separated: "set2_lp_iterm (nu helper_slot) \<inter> set2_lp_iterm (lp_ieval ?head rho)={}"
  using lpp_checked_body_output_separate_head[OF fresh_map mgu finite_subst, of k eta, unfolded equation]
  by (simp add: target_env)
 have helper_free: "\<exists>u. nu helper_slot=LPIVar u"
  using lpp_checked_body_output_free[OF fresh_map mgu, of k eta] by (simp add: target_env)
 have coordinate_value: "nu w=rho v"
  if "lpp_check_clause_coordinate l (Var v) (Var w) bindings" for v w
  using lpp_checked_clause_coordinate_value[OF that, of k eta sigma rho]
  by (simp add: target_env)
 have coordinates: "nu input_slot=rho x" "nu parameter_slot=rho n"
   "nu tail_slot=rho y" "nu caller_slot=rho m"
  using checked by (auto simp: lpp_check_recursive_entry_coordinates_def intro: coordinate_value)
 obtain tail_length where tail: "lpp_list_length (rho y) tail_length"
  using lpp_list_head_tail_observation[OF spine actual] by blast
 obtain u v where outputs: "nu helper_slot=LPIVar u" "nu caller_slot=LPIVar v"
  using helper_free preserved output_value coordinates by (auto simp: lpc_free_knowledge_def)
 have different: "u\<noteq>v" using separated outputs coordinates by auto
 show ?thesis
  using tracked parameter_value finite_head tail outputs different separated coordinates
  by (auto simp: lpp_recursive_entry_def)
qed

ML \<open>
val checked = @{thms lpp_checked_recursive_entry};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive entry" else ();
\<close>
end
