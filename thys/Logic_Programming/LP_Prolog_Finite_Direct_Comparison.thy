theory LP_Prolog_Finite_Direct_Comparison
 imports LP_Prolog_Stable_Primitive LP_Prolog_Stable_Primitive_Domain
   LP_Prolog_Finite_Direct_Invariant
begin

lemma lpp_finite_comparison_source_domain:
 assumes name: "lpp_comparison_descriptor f comparison reversed"
   and finite: "lpp_finite_term a" "lpp_finite_term b"
 shows "lpp_finite_source_domain f [a,b]"
proof (rule lpp_finite_source_domain_extends)
 show "lpp_integer_source_domain f [a,b]"
   using name finite by (cases comparison; cases reversed;
     auto simp: lpp_finite_compare_error_def)
qed

fun lpp_check_finite_direct_primitive where
 "lpp_check_finite_direct_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPEComparison evidence yes_facts no_facts error_facts) =
      lpp_check_comparison_links T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context
        (lppfc_predicate evidence) (lppfc_comparison evidence) (lppfc_reversed evidence)
        (lppfc_left evidence) (lppfc_right evidence) (lppfc_goals evidence) (lppfc_active evidence)
        (lppfc_saved evidence) (lppfc_yes evidence) (lppfc_no evidence) (lppfc_error evidence)"
| "lpp_check_finite_direct_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action =
    lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"

lemma lpp_finite_direct_primitive_sound:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
   and program: "lpp_check_transfer_program T SP receipts"
   and checked: "lpp_check_finite_direct_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
   and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
   and free: "lpc_free_knowledge (set F) eta"
   and observed: "lpp_stable_context_holds operation SP source_context eta"
   and step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
 shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u"
proof (cases "\<exists>e y n r. action=LPPEComparison e y n r")
 case True
 then obtain e y n r where action: "action=LPPEComparison e y n r" by blast
 have links: "lpp_check_comparison_links T y n r fuel Q nds states contexts Fs nd F ss source_context
        (lppfc_predicate e) (lppfc_comparison e) (lppfc_reversed e)
        (lppfc_left e) (lppfc_right e) (lppfc_goals e) (lppfc_active e)
        (lppfc_saved e) (lppfc_yes e) (lppfc_no e) (lppfc_error e)"
   using checked by (simp add: action)
 show ?thesis using lpp_stable_comparison_links_sound[OF compatible program links known free observed step] by blast
next
 case False
 have legacy: "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
   using checked False by (cases action) auto
 show ?thesis using lpp_stable_primitive_sound[OF compatible program legacy known free observed step] by blast
qed

lemma lpp_finite_direct_primitive_domain:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
   and program: "lpp_check_transfer_program T SP receipts"
   and checked: "lpp_check_finite_direct_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
   and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
   and observed: "lpp_stable_context_holds operation SP source_context eta"
   and invariant: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
 shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
proof (cases "\<exists>e y n r. action=LPPEComparison e y n r")
 case True
 then obtain e y n r where action: "action=LPPEComparison e y n r" by blast
 have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser (lppfc_predicate e)) [lppfc_left e,lppfc_right e])#lppfc_goals e),lppfc_active e)#lppfc_saved e"
   and name: "lpp_comparison_descriptor (lppfc_predicate e) (lppfc_comparison e) (lppfc_reversed e)"
   using checked by (auto simp: action lpp_check_comparison_links_def)
 have finite: "lpp_finite_term (lp_ieval (lppfc_left e) eta)" "lpp_finite_term (lp_ieval (lppfc_right e) eta)"
   using invariant by (auto simp: shape lpc_return_eval_def
     lpp_finite_direct_invariant_def lpp_finite_direct_state_def)
 have domain: "lpp_finite_source_domain (lppfc_predicate e)
    [lp_ieval (lppfc_left e) eta,lp_ieval (lppfc_right e) eta]"
   by (rule lpp_finite_comparison_source_domain[OF name finite])
 show ?thesis using domain by (simp add: shape lpc_return_eval_def)
next
 case False
 have legacy: "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
   using checked False by (cases action) auto
 show ?thesis by (rule lpp_stable_primitive_domain[OF compatible program legacy known observed])
qed

ML \<open>
val checked = [@{thm lpp_finite_comparison_source_domain},
 @{thm lpp_finite_direct_primitive_sound}, @{thm lpp_finite_direct_primitive_domain}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite comparison primitive" else ();
\<close>
end
