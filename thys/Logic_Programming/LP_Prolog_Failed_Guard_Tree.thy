theory LP_Prolog_Failed_Guard_Tree
 imports LP_Prolog_Scalar_Recurrence_Failure LP_Prolog_Finite_Choice
begin

datatype lpp_failed_guard_tree =
 LPPFailedGuard lpp_scalar_guard
 | LPPFailedThen lpp_scalar_guard lpp_failed_guard_tree
 | LPPFailedChoice lpp_failed_guard_tree lpp_failed_guard_tree

definition lpp_guard_atom where
 "lpp_guard_atom g=Fun (LPCUser (lpp_scalar_guard_symbol g)) (lpp_scalar_guard_terms g)"
fun lpp_failed_tree_term where
 "lpp_failed_tree_term (LPPFailedGuard g)=lpp_guard_atom g"
| "lpp_failed_tree_term (LPPFailedThen g t)=Fun LPCComma [lpp_guard_atom g,lpp_failed_tree_term t]"
| "lpp_failed_tree_term (LPPFailedChoice a b)=Fun (LPCUser ''2:;'') [lpp_failed_tree_term a,lpp_failed_tree_term b]"
fun lpp_failed_tree_goals where
 "lpp_failed_tree_goals (LPPFailedGuard g)=[lpp_scalar_guard_goal g]"
| "lpp_failed_tree_goals (LPPFailedThen g t)=lpp_scalar_guard_goal g#lpp_failed_tree_goals t"
| "lpp_failed_tree_goals (LPPFailedChoice a b)=[LPCAtom (lpp_failed_tree_term (LPPFailedChoice a b))]"
fun lpp_failed_tree_check where
 "lpp_failed_tree_check V (LPPFailedGuard g)=(lpp_scalar_guard_check V g=Some False)"
| "lpp_failed_tree_check V (LPPFailedThen g t)=(lpp_scalar_guard_check V g=Some True \<and> lpp_failed_tree_check V t)"
| "lpp_failed_tree_check V (LPPFailedChoice a b)=(lpp_failed_tree_check V a \<and> lpp_failed_tree_check V b)"

lemma lpp_failed_tree_lower:
 "lpp_branch_lower (lp_ieval (lpp_failed_tree_term t) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals t))"
proof (induct t)
 case (LPPFailedGuard g)
 show ?case by (simp add: lpp_guard_atom_def lpp_scalar_guard_goal_def; rule lpp_branch_lower.atom)
next
 case (LPPFailedThen g t)
 have first: "lpp_branch_lower (lp_ieval (lpp_guard_atom g) eta)
   [lp_cut_map (\<lambda>t. lp_ieval t eta) (lpp_scalar_guard_goal g)]"
   by (simp add: lpp_guard_atom_def lpp_scalar_guard_goal_def; rule lpp_branch_lower.atom)
 show ?case using lpp_branch_lower.conjunction[OF first LPPFailedThen.hyps] by simp
next
 case (LPPFailedChoice a b)
 show ?case by (simp; rule lpp_branch_lower.atom)
qed

lemma lpp_checked_guard_not_if:
 "lpp_scalar_guard_check V g=Some held \<Longrightarrow> lpp_scalar_guard_symbol g\<noteq>''2:->''"
 by (cases g) (auto split: option.splits prod.splits if_splits)

lemma lpp_failed_tree_choice_left:
 "lpp_failed_tree_check V t \<Longrightarrow> lpp_choice_left (lp_ieval (lpp_failed_tree_term t) eta)"
 by (cases t) (auto simp: lpp_guard_atom_def dest: lpp_checked_guard_not_if)

lemma lpp_failed_tree_choice_step:
 assumes checked: "lpp_failed_tree_check V a"
 shows "(LPCGoals (LPCAtom (lp_ieval (lpp_failed_tree_term (LPPFailedChoice a b)) eta)#gs)#es,
   LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals a)@gs)#
   LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals b)@gs)#es)\<in>
   lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 let ?U = "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)"
 let ?a = "lp_ieval (lpp_failed_tree_term a) eta"
 let ?b = "lp_ieval (lpp_failed_tree_term b) eta"
 let ?left = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals a)"
 let ?right = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals b)"
 have outcome: "?U ''2:;'' [?a,?b] (LPPBuiltinChoice ?left ?right)"
   using lpp_failed_tree_lower[of a eta] lpp_failed_tree_lower[of b eta]
     lpp_failed_tree_choice_left[OF checked, of eta]
   by (auto simp: lpp_stable_source_builtin_def lpp_finite_source_builtin_def
       lpp_disequality_predicate_def lpp_branch_outcome_def)
 have plain: "list_all lpp_plain_goal (?left@?right)"
   using lpp_branch_lower_plain[OF lpp_failed_tree_lower[of a eta]]
     lpp_branch_lower_plain[OF lpp_failed_tree_lower[of b eta]] by simp
 have step: "(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:;'') [?a,?b])#gs)#es,
     LPCGoals (?left@gs)#LPCGoals (?right@gs)#es)\<in>lpp_atomic_source P lpp_builtin_signature ?U"
   by (rule lpp_atomic_source.choice[where U="?U", OF outcome plain])
 have signature: "(''2:;'',Suc (Suc 0))\<in>lpp_builtin_signature" by (simp add: lpp_builtin_signature_def)
 show ?thesis using step signature
   by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
qed

lemma lpp_failed_tree_sound:
 assumes checked: "lpp_failed_tree_check V tree"
   and parameters: "\<And>x w. V x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
 shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals tree)@gs)#es,es)\<in>
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
 using checked
proof (induct tree arbitrary: gs es)
 case (LPPFailedGuard g)
 show ?case using lpp_scalar_guard_step[where value_table=V and eta=eta, OF _ parameters, where g=g and held=False and gs=gs and es=es and P=P]
   LPPFailedGuard.prems by (auto intro: r_into_trancl)
next
 case (LPPFailedThen g tree)
 let ?rest = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals tree)@gs"
 have step: "(LPCGoals (lp_cut_map (\<lambda>t. lp_ieval t eta) (lpp_scalar_guard_goal g)#?rest)#es,
     LPCGoals ?rest#es)\<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
   using lpp_scalar_guard_step[where value_table=V and eta=eta, OF _ parameters, where g=g and held=True and gs="?rest" and es=es and P=P] LPPFailedThen.prems by simp
 show ?case using LPPFailedThen.hyps[of gs es] LPPFailedThen.prems
   trancl_trans[OF r_into_trancl[OF step]] by auto
next
 case (LPPFailedChoice a b)
 let ?right = "LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals b)@gs)#es"
 have left: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (lpp_failed_tree_goals a)@gs)#?right,?right)\<in>
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   using LPPFailedChoice.hyps(1)[of gs "?right"] LPPFailedChoice.prems by simp
 have right: "(?right,es)\<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   using LPPFailedChoice.hyps(2)[of gs es] LPPFailedChoice.prems by simp
 have a_checked: "lpp_failed_tree_check V a" using LPPFailedChoice.prems by simp
 show ?case using trancl_trans[OF r_into_trancl[OF lpp_failed_tree_choice_step[OF a_checked, where b=b and eta=eta and gs=gs and es=es and P=P and fallback=fallback]]
   trancl_trans[OF left right]] by simp
qed

ML \<open>
val checked = [@{thm lpp_failed_tree_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted failed-guard tree" else ();
\<close>
end
