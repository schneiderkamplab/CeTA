theory LP_Prolog_Finite_Local_State
 imports LP_Prolog_Finite_Head_Check LP_Prolog_Finite_Direct_Invariant
begin

fun lpp_check_finite_resolution_entry where
 "lpp_check_finite_resolution_entry G P (LPCClause (LPCAtom (Fun f ats)#gs) c m) =
   (if c<length P then
     (case fst (P!c) of Var x \<Rightarrow> False | Fun h hs \<Rightarrow>
       f\<noteq>h \<or> length ats\<noteq>length hs \<or>
       (lpp_check_finite_head G ats hs \<and> list_all lpp_direct_source_goal (snd (P!c))))
    else True)"
| "lpp_check_finite_resolution_entry G P (LPCClause (LPCAtom (Var x)#gs) c m) = False"
| "lpp_check_finite_resolution_entry G P e = True"

lemma lpp_checked_resolution_entry_finite:
 assumes checked: "lpp_check_finite_resolution_entry G P e"
   and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
   and shape: "lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e=LPCClause (LPCAtom a#gs) c m"
   and index: "c<length P"
   and mgu: "lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) sigma rho"
   and finite: "lpp_finite_direct_entry (lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e)"
 shows "lpp_finite_direct_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 obtain z rest where entry: "e=LPCClause (z#rest) c m"
   using shape by (cases e; auto split: list.splits)
 obtain t where goal: "z=LPCAtom t"
   using shape by (cases z; auto simp: entry)
 obtain f ats where term_shape: "t=Fun f ats"
   using checked by (cases t; auto simp: entry goal)
 have template: "e=LPCClause (LPCAtom (Fun f ats)#rest) c m"
   by (simp add: entry goal term_shape)
 have a: "a=LPIFun f (map (\<lambda>t. lp_ieval t eta) ats)"
   using shape by (simp add: template)
 obtain h hs where head: "fst (P!c)=Fun h hs"
   using checked index by (auto simp: template split: term.splits)
 have equal: "lp_isubst a sigma=lp_ieval (fst (P!c)) rho"
   using mgu by (simp add: lpc_mgu_resolve_def)
 have symbol: "f=h" and lengths: "length ats=length hs"
   using equal by (auto simp: a head dest: arg_cong[where f=length])
 have check: "lpp_check_finite_head G ats hs"
   and body: "list_all lpp_direct_source_goal (snd (P!c))"
   using checked index symbol lengths by (simp_all add: template head)
 have arguments: "list_all lpp_finite_term (map (\<lambda>t. lp_ieval t eta) ats)"
   and continuation: "lpp_finite_direct_goals gs"
   using finite by (simp_all add: shape a)
 show ?thesis
   by (rule lpp_checked_head_finite_direct_goals[OF check known mgu[unfolded a head symbol] arguments continuation body])
qed


fun lpp_check_finite_resolution_state where
 "lpp_check_finite_resolution_state G P [] = True"
| "lpp_check_finite_resolution_state G P ((e,active)#saved) = lpp_check_finite_resolution_entry G P e"

lemma lpp_finite_local_ordinary_step:
 assumes checked: "lpp_check_finite_resolution_state G P ss"
   and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
   and transition: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
   and state: "lpp_finite_direct_state (lpc_return_eval eta ss)"
 shows "lpp_finite_direct_state tt"
 using transition state
proof (cases rule: lpc_answer_transition.cases)
 case (resolve c a gs sigma rho m env es)
 obtain e active saved where source: "ss=(e,active)#saved"
   and shape: "lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e=LPCClause (LPCAtom a#gs) c m"
   using resolve by (cases ss; auto simp: lpc_return_eval_def split: prod.splits)
 have check: "lpp_check_finite_resolution_entry G P e"
   using checked by (simp add: source)
 have finite: "lpp_finite_direct_entry (lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e)"
   using state by (simp add: source lpc_return_eval_def lpp_finite_direct_state_def)
 have goals: "lpp_finite_direct_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
   by (rule lpp_checked_resolution_entry_finite[OF check known shape _ _ finite])
     (use resolve in auto)
 show ?thesis using resolve state goals by (auto simp: lpp_finite_direct_state_def)
next
 case (unify a b gs sigma env es)
 then show ?thesis using state lpp_finite_direct_scalar_unify[where nu="\<lambda>x. lp_isubst (env x) sigma"]
   by fastforce
qed (auto simp: lpp_finite_direct_state_def list_all_iff
  dest: lpp_finite_direct_prune[unfolded lpp_finite_direct_state_def list_all_iff])

ML \<open>
val checked = [@{thm lpp_checked_resolution_entry_finite},
 @{thm lpp_finite_local_ordinary_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted local resolution transport" else ();
\<close>
end
