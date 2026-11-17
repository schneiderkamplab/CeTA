theory LP_Prolog_Univ_Decomposition
 imports LP_Prolog_Constructor_Arguments LP_Cut_MGU_Knowledge
begin

text \<open>Nonvariable univ decomposition is an observation followed by the
shared rational MGU operation. The constructor-name encoding remains explicit.
This is a termination overapproximation of outcomes: uncaught errors are kept,
and normal failure requires absence of a unifier. Variable-input construction
is outside this domain and must retain its unsupported-source obligation.
No finiteness of the substituted input follows merely from its old finiteness:
requested_list aliases can create cycles.\<close>

fun lpp_univ_decomposition where
 "lpp_univ_decomposition constructor_name_encoding (LPIVar x) = None"
| "lpp_univ_decomposition constructor_name_encoding (LPIFun f ts) =
   Some (lpp_argument_list (LPIFun (constructor_name_encoding f) [] # ts))"

lemma lpp_univ_decomposition_subst:
 assumes "lpp_univ_decomposition constructor_name_encoding input_value = Some parts"
 shows "lpp_univ_decomposition constructor_name_encoding (lp_isubst input_value sigma) = Some (lp_isubst parts sigma)"
 using assms by (cases "input_value") (auto simp: lpp_argument_list_subst)

definition lpp_univ_decompose_outcome ::
 "(string lp_cut_symbol \<Rightarrow> string lp_cut_symbol) \<Rightarrow>
  (string lp_cut_symbol,string) lp_iterm \<Rightarrow>
  (string lp_cut_symbol,string) lp_iterm \<Rightarrow>
  (string,string) lpp_builtin_result \<Rightarrow> bool" where
 "lpp_univ_decompose_outcome constructor_name_encoding input_value requested_list outcome_value =
   (\<exists>parts. lpp_univ_decomposition constructor_name_encoding input_value = Some parts \<and>
    (case outcome_value of
       LPPBuiltinSuccess mu \<Rightarrow> (\<forall>gs. lpc_mgu_unify requested_list parts gs mu)
     | LPPBuiltinFailure \<Rightarrow> \<not>(\<exists>sigma :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm. lp_isubst requested_list sigma = lp_isubst parts sigma)
     | LPPBuiltinError \<Rightarrow> True
     | _ \<Rightarrow> False))"

lemma lpp_univ_success_unifies:
 assumes outcome: "lpp_univ_decompose_outcome constructor_name_encoding input_value requested_list (LPPBuiltinSuccess mu)"
 shows "\<exists>parts. lpp_univ_decomposition constructor_name_encoding input_value = Some parts \<and>
   lp_isubst requested_list mu = lp_isubst parts mu"
 using outcome by (auto simp: lpp_univ_decompose_outcome_def lpc_mgu_unify_def)

lemma lpp_univ_success_observation:
 assumes outcome: "lpp_univ_decompose_outcome constructor_name_encoding input_value
   (LPIFun (LPCUser ''2:prolog_data_2e'') [name_term,arglist]) (LPPBuiltinSuccess mu)"
 shows "lpp_functor_observation constructor_name_encoding (lp_isubst input_value mu)
   (lp_isubst name_term mu) (lp_isubst arglist mu)"
 using lpp_univ_success_unifies[OF outcome]
 by (cases "input_value") (auto simp: lpp_functor_observation_exact lpp_argument_list_subst)

lemma lpp_univ_failure_has_no_success:
 assumes "lpp_univ_decompose_outcome constructor_name_encoding input_value requested_list LPPBuiltinFailure"
 shows "\<not> lpp_univ_decompose_outcome constructor_name_encoding input_value requested_list (LPPBuiltinSuccess mu)"
 using assms by (auto simp: lpp_univ_decompose_outcome_def lpc_mgu_unify_def)

lemma lpp_univ_variable_input_unsupported:
 "\<not> lpp_univ_decompose_outcome constructor_name_encoding (LPIVar x) requested_list outcome_value"
 by (simp add: lpp_univ_decompose_outcome_def)

lemma lpp_univ_nonvar_error_retained:
 "lpp_univ_decompose_outcome constructor_name_encoding (LPIFun f ts) requested_list LPPBuiltinError"
 by (simp add: lpp_univ_decompose_outcome_def)

lemma lpp_univ_success_keeps_saved_answers:
 assumes operation: "U ''2:=..'' [input_value,requested_list] (LPPBuiltinSuccess mu)"
 shows "lpp_answer_transition P B U
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [input_value,requested_list])#gs),eta)#saved)
   None ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs),
     \<lambda>x. lp_isubst (eta x) mu)#saved)"
 by (rule lpp_answer_transition.success) (rule operation)


text \<open>A free requested functor name covers both runtime input cases:
nonvariable input uses decomposition; variable input raises an instantiation
error. This does not cover constructing a term from a known functor name.\<close>
definition lpp_univ_view_domain where
 "lpp_univ_view_domain input_value requested_list =
  ((\<exists>f ts. input_value=LPIFun f ts) \<or>
   (\<exists>x. input_value=LPIVar x \<and>
     ((\<exists>y. requested_list=LPIVar y) \<or>
      (\<exists>y tail. requested_list=LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar y,tail]))))"

fun lpp_check_univ_view_domain where
 "lpp_check_univ_view_domain F (Fun f ts) requested_list = True"
| "lpp_check_univ_view_domain F (Var x) (Var y) = (y\<in>set F)"
| "lpp_check_univ_view_domain F (Var x) (Fun f [Var y,tail]) =
    (f=LPCUser ''2:prolog_data_2e'' \<and> y\<in>set F)"
| "lpp_check_univ_view_domain F input_value requested_list = False"

lemma lpp_univ_free_name_domain:
 "lpp_univ_view_domain input_value (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar y,tail])"
 by (cases "input_value") (auto simp: lpp_univ_view_domain_def)

lemma lpp_univ_free_list_domain:
 "lpp_univ_view_domain input_value (LPIVar y)"
 by (cases "input_value") (auto simp: lpp_univ_view_domain_def)

lemma lpp_univ_nonvar_domain[simp]:
 "lpp_univ_view_domain (LPIFun f ts) requested_list"
 by (auto simp: lpp_univ_view_domain_def)

lemma lpp_check_univ_view_domain_sound:
 assumes checked: "lpp_check_univ_view_domain F input_value requested_list"
 and free: "lpc_free_knowledge (set F) eta"
 shows "lpp_univ_view_domain (lp_ieval input_value eta) (lp_ieval requested_list eta)"
 using checked free
 apply (induction F input_value requested_list rule: lpp_check_univ_view_domain.induct)
 apply (auto simp: lpc_free_knowledge_def intro: lpp_univ_free_name_domain lpp_univ_free_list_domain)
 by (metis lpp_univ_free_name_domain lpp_univ_free_list_domain)+

fun lpp_univ_view_outcome where
 "lpp_univ_view_outcome names (LPIFun f ts) requested_list outcome_value =
   lpp_univ_decompose_outcome names (LPIFun f ts) requested_list outcome_value"
| "lpp_univ_view_outcome names (LPIVar x) requested_list outcome_value =
   (((\<exists>y. requested_list=LPIVar y) \<or>
     (\<exists>y tail. requested_list=LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar y,tail])) \<and>
    outcome_value=LPPBuiltinError)"

lemma lpp_univ_view_success_observation:
 "lpp_univ_view_outcome names input_value
    (LPIFun (LPCUser ''2:prolog_data_2e'') [name_term,arglist]) (LPPBuiltinSuccess mu) \<Longrightarrow>
  lpp_functor_observation names (lp_isubst input_value mu)
    (lp_isubst name_term mu) (lp_isubst arglist mu)"
 by (cases "input_value") (auto dest: lpp_univ_success_observation)

lemma lpp_univ_view_free_input_error:
 "lpp_univ_view_outcome names (LPIVar x)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar y,tail]) LPPBuiltinError"
 by simp


lemma lpp_univ_free_head_checked:
 "lpp_check_univ_view_domain [''Name''] (Var ''Input'')
   (Fun (LPCUser ''2:prolog_data_2e'') [Var ''Name'',Var ''Arguments''])"
 by simp

lemma lpp_univ_free_list_checked:
 "lpp_check_univ_view_domain [''List''] (Var ''Input'') (Var ''List'')"
 by simp

lemma lpp_univ_missing_free_head_rejected:
 "\<not> lpp_check_univ_view_domain [] (Var ''Input'')
   (Fun (LPCUser ''2:prolog_data_2e'') [Var ''Name'',Var ''Arguments''])"
 by simp

lemma lpp_univ_unknown_list_rejected:
 "\<not> lpp_check_univ_view_domain [] (Var ''Input'') (Var ''List'')"
 by simp

lemma lpp_univ_known_name_construction_stays_open:
 "\<not> lpp_check_univ_view_domain [] (Var ''Input'')
   (Fun (LPCUser ''2:prolog_data_2e'') [Fun (LPCUser ''0:prolog_data_66'') [],Var ''Arguments''])"
 by simp

ML \<open>
val checked = [@{thm lpp_check_univ_view_domain_sound}, @{thm lpp_univ_view_success_observation},
 @{thm lpp_univ_decomposition_subst}, @{thm lpp_univ_success_observation},
 @{thm lpp_univ_failure_has_no_success}, @{thm lpp_univ_success_keeps_saved_answers}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ decomposition dependency" else ();
\<close>
end
