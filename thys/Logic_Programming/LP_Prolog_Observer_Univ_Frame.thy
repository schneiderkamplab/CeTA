theory LP_Prolog_Observer_Univ_Frame
 imports LP_Prolog_Observer_Domain_Module
begin

fun lpp_observer_univ_frame where
 "lpp_observer_univ_frame ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),env)#saved) = (f=''2:=..'')"
| "lpp_observer_univ_frame ss = False"

lemma lpp_observer_univ_frame_scope:
 "lpp_observer_univ_frame (lpc_return_scope r ss)=lpp_observer_univ_frame ss"
 by (induction ss rule: lpp_observer_univ_frame.induct) auto

lemma lpp_observer_univ_frame_scopes:
 "lpp_observer_univ_frame (lpc_return_scope_word swaps ss)=lpp_observer_univ_frame ss"
proof (induct swaps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons ab swaps)
 obtain a b where pair: "ab=(a,b)" by (cases ab) auto
 show ?case by (simp only: pair lpc_return_scope_word.simps Cons.hyps lpp_observer_univ_frame_scope)
qed

lemma lpp_fresh_matching_resolution_univ_frame:
 assumes matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and step: "lpp_domain_answers P B U D
   ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,env)#saved) event tt"
 shows "lpp_observer_univ_frame tt"
proof -
 have possible: "\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. \<exists>rho.
   lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  by (rule lp_cut_check_match_sound[OF matching])
 obtain body_rest where body: "snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'') [Var x,
   Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_rest"
  using fresh by (auto simp: lpp_check_fresh_univ_clause_def)
 have base: "lpc_answer_transition P ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,env)#saved) event tt"
  by (rule lpp_observer_clause_base[OF step])
 show ?thesis using base possible by (cases rule: lpc_answer_transition.cases) (auto simp: body)
qed
end
