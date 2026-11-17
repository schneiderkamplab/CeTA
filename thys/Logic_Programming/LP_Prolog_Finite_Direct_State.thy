theory LP_Prolog_Finite_Direct_State
 imports LP_Prolog_Finite_Goal_Transport LP_Cut_Answers
begin

fun lpp_direct_source_goal where
 "lpp_direct_source_goal (LPCAtom (Fun f ts)) = True"
| "lpp_direct_source_goal (LPCAtom (Var x)) = False"
| "lpp_direct_source_goal (LPCUnify a b) = False"
| "lpp_direct_source_goal (LPCMeta a) = False"
| "lpp_direct_source_goal (LPCExpand a m) = False"
| "lpp_direct_source_goal g = True"

fun lpp_finite_direct_goal where
 "lpp_finite_direct_goal (LPCAtom a) = (lpp_finite_term a \<and> (\<exists>f ts. a=LPIFun f ts))"
| "lpp_finite_direct_goal (LPCUnify a b) = False"
| "lpp_finite_direct_goal (LPCMeta a) = False"
| "lpp_finite_direct_goal (LPCExpand a m) = False"
| "lpp_finite_direct_goal g = True"

abbreviation lpp_finite_direct_goals where
 "lpp_finite_direct_goals gs \<equiv> list_all lpp_finite_direct_goal gs"
fun lpp_finite_direct_entry where
 "lpp_finite_direct_entry (LPCGoals gs) = lpp_finite_direct_goals gs"
| "lpp_finite_direct_entry (LPCClause gs c m) = lpp_finite_direct_goals gs"
| "lpp_finite_direct_entry (LPCBarrier m) = True"
definition lpp_finite_direct_state where
 "lpp_finite_direct_state ss = list_all (\<lambda>frame. lpp_finite_direct_entry (fst frame)) ss"
definition lpp_finite_direct_program where
 "lpp_finite_direct_program P = list_all (\<lambda>(h,bs). \<exists>f H.
    h=Fun f (map Var H) \<and> distinct H \<and> list_all lpp_direct_source_goal bs) P"

lemma lpp_finite_direct_goal_terms:
 "lpp_finite_direct_goal g \<Longrightarrow> list_all lpp_finite_term (lp_cut_terms g)"
 by (cases g) auto

lemma lpp_finite_direct_goals_terms:
 "lpp_finite_direct_goals gs \<Longrightarrow> lpp_finite_goals gs"
 using lpp_finite_direct_goal_terms unfolding lpp_finite_goals_def list_all_iff by blast

lemma lpp_direct_bind_shape:
 "lpp_direct_source_goal g \<Longrightarrow>
  (case lp_cut_bind m (\<lambda>t. lp_ieval t rho) g of LPCAtom a \<Rightarrow> \<exists>f ts. a=LPIFun f ts
   | LPCUnify a b \<Rightarrow> False | LPCMeta a \<Rightarrow> False | LPCExpand a m \<Rightarrow> False | _ \<Rightarrow> True)"
 by (cases g; auto; metis lpp_direct_source_goal.simps lp_ieval.simps term.exhaust)

lemma lpp_direct_map_shape:
 assumes shape: "lpp_finite_direct_goal g"
 shows "(case lp_cut_map (\<lambda>t. lp_isubst t sigma) g of LPCAtom a \<Rightarrow> \<exists>f ts. a=LPIFun f ts
   | LPCUnify a b \<Rightarrow> False | LPCMeta a \<Rightarrow> False | LPCExpand a m \<Rightarrow> False | _ \<Rightarrow> True)"
 using shape by (cases g) auto

lemma lpp_finite_direct_intro:
 "list_all lpp_finite_term (lp_cut_terms g) \<Longrightarrow>
  (case g of LPCAtom a \<Rightarrow> \<exists>f ts. a=LPIFun f ts
   | LPCUnify a b \<Rightarrow> False | LPCMeta a \<Rightarrow> False
   | LPCExpand a m \<Rightarrow> False | _ \<Rightarrow> True) \<Longrightarrow>
  lpp_finite_direct_goal g"
 by (cases g) auto

lemma lpp_finite_direct_resolution:
 assumes mgu: "lpc_mgu_resolve a gs (Fun f (map Var H)) bs sigma rho"
   and selected: "lpp_finite_direct_goal (LPCAtom a)"
   and continuation: "lpp_finite_direct_goals gs"
   and distinct: "distinct H"
   and body: "list_all lpp_direct_source_goal bs"
 shows "lpp_finite_direct_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 obtain g actuals where a: "a=LPIFun g actuals" and finite: "list_all lpp_finite_term actuals"
   using selected by auto
 have equation: "lp_isubst a sigma=lp_ieval (Fun f (map Var H)) rho"
   using mgu by (simp add: lpc_mgu_resolve_def)
 have head: "g=f" and lengths: "length H=length actuals"
   using equation by (auto simp: a dest: arg_cong[where f=length])
 have terms: "lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
     map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
   using mgu unfolding a head
   by (rule lpp_variable_head_finite_goals[OF _ lengths distinct finite
       lpp_finite_direct_goals_terms[OF continuation]])
 have bound: "lpp_finite_direct_goal (lp_cut_bind m (\<lambda>t. lp_ieval t rho) g)"
   if "g\<in>set bs" for g
 proof (rule lpp_finite_direct_intro)
  show "list_all lpp_finite_term (lp_cut_terms (lp_cut_bind m (\<lambda>t. lp_ieval t rho) g))"
    using terms that by (auto simp: lpp_finite_goals_def list_all_iff)
  show "case lp_cut_bind m (\<lambda>t. lp_ieval t rho) g of
    LPCAtom a \<Rightarrow> \<exists>f ts. a=LPIFun f ts | LPCMeta a \<Rightarrow> False
    | LPCExpand a m \<Rightarrow> False | LPCUnify a b \<Rightarrow> False | _ \<Rightarrow> True"
    by (rule lpp_direct_bind_shape) (use body that in \<open>auto simp: list_all_iff\<close>)
 qed
 have mapped: "lpp_finite_direct_goal (lp_cut_map (\<lambda>t. lp_isubst t sigma) g)"
   if "g\<in>set gs" for g
 proof (rule lpp_finite_direct_intro)
  show "list_all lpp_finite_term (lp_cut_terms (lp_cut_map (\<lambda>t. lp_isubst t sigma) g))"
    using terms that by (auto simp: lpp_finite_goals_def list_all_iff)
  show "case lp_cut_map (\<lambda>t. lp_isubst t sigma) g of
    LPCAtom a \<Rightarrow> \<exists>f ts. a=LPIFun f ts | LPCMeta a \<Rightarrow> False
    | LPCExpand a m \<Rightarrow> False | LPCUnify a b \<Rightarrow> False | _ \<Rightarrow> True"
    by (rule lpp_direct_map_shape) (use continuation that in \<open>auto simp: list_all_iff\<close>)
 qed
 show ?thesis using bound mapped by (auto simp: list_all_iff)
qed
lemma lpp_finite_direct_resolve_state:
 assumes program: "lpp_finite_direct_program P"
   and index: "c<length P"
   and mgu: "lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) sigma rho"
   and state: "lpp_finite_direct_state ((LPCClause (LPCAtom a#gs) c m,eta)#es)"
 shows "lpp_finite_direct_state ((LPCGoals
   (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
    map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),nu)#es)"
proof -
 obtain f H where head: "fst (P!c)=Fun f (map Var H)" and distinct: "distinct H"
   and body: "list_all lpp_direct_source_goal (snd (P!c))"
   using program nth_mem[OF index] by (auto simp: lpp_finite_direct_program_def list_all_iff case_prod_beta)
 have selected: "lpp_finite_direct_goal (LPCAtom a)" and rest: "lpp_finite_direct_goals gs"
   and saved: "lpp_finite_direct_state es"
   using state by (auto simp: lpp_finite_direct_state_def)
 have resolution: "lpc_mgu_resolve a gs (Fun f (map Var H)) (snd (P!c)) sigma rho"
   using mgu head by simp
 show ?thesis using lpp_finite_direct_resolution[OF resolution selected rest distinct body] saved
   by (simp add: lpp_finite_direct_state_def)
qed

lemma lpp_finite_direct_prune:
 "lpp_finite_direct_state es \<Longrightarrow> lpp_finite_direct_state (lpc_answer_prune m es)"
 by (induct es) (auto simp: lpp_finite_direct_state_def split: prod.splits lp_cut_entry.splits if_splits)

lemma lpp_finite_direct_ordinary_step:
 assumes program: "lpp_finite_direct_program P"
   and transition: "lpc_answer_transition P ss event tt"
   and state: "lpp_finite_direct_state ss"
 shows "lpp_finite_direct_state tt"
 using transition state
proof (cases rule: lpc_answer_transition.cases)
 case (resolve c a gs sigma rho m eta es)
 then show ?thesis using state lpp_finite_direct_resolve_state[where nu="\<lambda>x. lp_isubst (eta x) sigma", OF program]
   by fastforce
qed (auto simp: lpp_finite_direct_state_def list_all_iff
  dest: lpp_finite_direct_prune[unfolded lpp_finite_direct_state_def list_all_iff])

ML \<open>
val checked = [@{thm lpp_finite_direct_ordinary_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite direct source transport" else ();
\<close>

end
