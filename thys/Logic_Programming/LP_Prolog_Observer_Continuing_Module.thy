theory LP_Prolog_Observer_Continuing_Module
 imports LP_Prolog_Observer_Continuing_Univ
begin

fun lpp_observer_has_continuation where
 "lpp_observer_has_continuation ((LPCGoals (g#h#gs),env)#saved) = True"
| "lpp_observer_has_continuation ss = False"



lemma lpp_observer_continuing_equality_frame_scope:
 "lpp_observer_continuing_equality_frame (lpc_return_scope r ss)=lpp_observer_continuing_equality_frame ss"
 by (induction ss rule: lpp_observer_continuing_equality_frame.induct) auto

lemma lpp_observer_continuing_equality_frame_scopes:
 "lpp_observer_continuing_equality_frame (lpc_return_scope_word swaps ss)=lpp_observer_continuing_equality_frame ss"
 proof (induct swaps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons ab swaps)
 obtain a b where pair: "ab=(a,b)" by (cases ab) auto
 show ?case by (simp only: pair lpc_return_scope_word.simps Cons.hyps lpp_observer_continuing_equality_frame_scope)
qed

lemma lpp_observer_continuing_equality_module_step:
 fixes SP :: "string lpp_success_clause list"
 assumes program: "lp_cut_source_program P"
 and coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    node_conditions lpp_finite_execution i"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions xs t"
 and finite: "lpp_finite_execution xs"
 and equality: "lpp_observer_continuing_equality_frame xs"
 and step: "lpc_answer_transition P xs ev ys"
 shows "ev=None \<and> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions ys u \<and> lpp_finite_execution ys)"
proof -
 obtain swaps i eta where bound: "i<length nds"
 and conditions: "node_conditions i eta"
 and shape: "lpc_return_scope_word swaps xs=lpc_return_eval eta (states!i)"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and subject: "t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
  using represented by (auto simp: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)
 have frame: "lpp_observer_continuing_equality_frame (lpc_return_eval eta (states!i))"
  using equality shape lpp_observer_continuing_equality_frame_scopes by metis
 have invariant: "lpp_finite_execution (lpc_return_eval eta (states!i))"
  using finite shape by (metis lpp_finite_execution_scope_word)
 have scoped: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev (lpc_return_scope_word swaps ys)"
  using lpc_answer_transition_scope_word[OF step program, of swaps] by (simp only: shape)
 have node: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    node_conditions lpp_finite_execution i"
  by (rule coverage[OF bound frame])
 obtain u more where silent: "ev=None" and edge: "(t,u)\<in>(lp_ild Q)\<^sup>+"
 and child: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_return_scope_word more (lpc_return_scope_word swaps ys)) u"
 and preserved: "lpp_finite_execution (lpc_return_scope_word swaps ys)"
  using node[unfolded lpp_observer_node_simulation_def, rule_format, OF conditions known free observed functors invariant scoped]
  unfolding subject lpp_premised_functor_module_rep_def by blast
 have rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions ys u"
  unfolding lpp_premised_functor_module_rep_def
  by (rule exI[of _ "swaps@more"]) (simp add: lpc_return_scope_word_append child)
 show ?thesis using silent edge rep preserved by (simp add: lpp_finite_execution_scope_word) blast
qed



lemma lpp_checked_continuing_univ_module_block:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved value_variable name_variable arguments_variable middle"
 and continuation: "gs\<noteq>[]"
 and separation_bound: "lpcl_target middle<length separation_contexts"
 and separation_transport: "lpp_check_separation_transport initialized_separation
   (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
 and separation_initialized: "\<And>f ts. lp_ieval input_template eta=LPIFun f ts \<Longrightarrow>
   list_all (lpp_separation_holds
     (eta(value_variable:=LPIFun f ts,name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)))
     initialized_separation"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and context_held: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"

 and domain: "lpp_univ_view_domain (lp_ieval input_template eta) (lp_ieval requested eta)"
 and finite: "lpp_finite_execution (lpc_return_eval eta ss)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ss) event result"
 and source_program: "lp_cut_source_program P"
 and coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 shows "event=None \<and> (result=[] \<or> (\<exists>u.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) result u))"
proof (rule lpp_checked_continuing_univ_source_block[OF compatible program checked continuation separation_bound separation_transport
 separation_initialized known free context_held functors domain finite step])
 fix xs t ev ys
 assume rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) xs t"
 and finite: "lpp_finite_execution xs"
 and frame: "lpp_observer_continuing_equality_frame xs"
 and step: "lpc_answer_transition P xs ev ys"
 show "\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) ys u \<and> lpp_finite_execution ys"
 proof -
  have simulated: "ev=None \<and> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) ys u \<and> lpp_finite_execution ys)"
   apply (rule lpp_observer_continuing_equality_module_step[OF source_program _ rep finite frame step])
   subgoal for i eta by (rule coverage[of i eta]) assumption+
   done
  show ?thesis using simulated by blast
 qed
qed



theorem lpp_checked_continuing_separation_univ_source_step:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
   (LPPFUniv value_var name_var args_var middle facts)"
 and continuation: "lpp_observer_has_continuation (states!i)"
 and extra: "lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and source_program: "lp_cut_source_program P"
 and coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_return_eval eta (states!i)) event result"
 shows "event=None \<and> (result=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) result u))"
proof -
 obtain a gs active saved where
  shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,Fun pair_symbol [output_name,output_args]])#gs),active)#saved"
  and incoming: "set [LPPSeparate a output_name,LPPSeparate a output_args]\<subseteq> set (separation_contexts!i)"
  and bound: "lpcl_target middle<length separation_contexts"
  and transport: "lpp_check_separation_transport
    [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]
    (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
  using lpp_checked_separation_univ_shape[OF extra] by blast
 have init: "lpp_check_univ_initialization value_var name_var args_var a (states!i) (contexts!i) (functor_contexts!i)"
   using checked by (auto simp: shape lpp_check_functor_source_action_def lpp_check_univ_evaluation_context_def)
 have separated: "list_all (lpp_separation_holds eta) [LPPSeparate a output_name,LPPSeparate a output_args]"
   using incoming conditions unfolding lpp_separation_node_conditions_def list_all_iff by blast
 have initialized: "list_all (lpp_separation_holds
     (eta(value_var:=LPIFun f ts,name_var:=LPIFun (names f) [],args_var:=lpp_argument_list ts)))
     [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]"
   if input: "lp_ieval a eta=LPIFun f ts" for f ts
   using lpp_univ_initializes_pair_separation[OF init[unfolded shape] input observed functors separated] by simp
 have check: "lpp_check_univ_evaluation_context T facts fuel Q nds states contexts functor_contexts Fs
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i)
   a (Fun pair_symbol [output_name,output_args]) gs active saved value_var name_var args_var middle"
  using checked by (simp add: shape lpp_check_functor_source_action_def)
 have dom_check: "lpp_check_univ_view_domain (Fs!i) a (Fun pair_symbol [output_name,output_args])"
  using check by (simp add: lpp_check_univ_evaluation_context_def)
 have domain: "lpp_univ_view_domain (lp_ieval a eta) (lp_ieval (Fun pair_symbol [output_name,output_args]) eta)"
  by (rule lpp_check_univ_view_domain_sound[OF dom_check free])
 have tail: "gs\<noteq>[]" using continuation by (cases gs) (simp_all add: shape)
 show ?thesis
  apply (rule lpp_checked_continuing_univ_module_block[OF compatible transfer check tail bound transport _
    known free observed functors domain finite step source_program])
  subgoal for f ts by (rule initialized[of f ts]) assumption
  subgoal for j nu by (rule coverage[of j nu]) assumption+
  done
qed

ML \<open>
val thms = @{thms lpp_checked_continuing_separation_univ_source_step};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted continuing module" else ();
\<close>
end
