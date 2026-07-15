(* Author: René Thiemann *)

text \<open>This theory uses the functions in CeTA to build a stand-alone
      commutation checker via Okui's criterion. It first converts 
      joinability problems to pure reachability problems
      (possible, since one side allows at most one multistep). 
      It is proven that strong commutation is equivalent to the 
      generated reachability problems. 

      Then an unverified incremental breadth-first-search-strategy for
      reachability is developed, that includes pruning with the help 
      of easy non-reachability criteria. Maybe, in future work also
      the BFS-search strategy is verified.\<close>

theory Okui_Commutation_Automation
  imports 
    Okui_Criterion_Impl
    Auxx.RenamingN_String
    TRS.Tcap_Impl
    TRS.Trs_Impl_More
begin


lift_definition ll_rules_to_wf_TRS :: "('f,'v)ll_rule list \<Rightarrow> ('f,'v)wfTRS" is "map To_rule" 
  by (transfer, force simp: Trs.wf_trs_def list_all_iff)

definition "automate_sim_cps_closed ren R S = do {
    let RR = ll_rules_to_wf_TRS R;
    let mstepR = mstep_rewrite_wf RR;
    let scps = filter (\<lambda> pair. fst pair \<noteq> snd pair) (Sim_cps_impl ren R S)
    in ( map (\<lambda> (s,t). (s, t, mstepR t)) scps)}" 

lemma get_TRS_ll_rules_to_wf_TRS: assumes "to_ll_rules R = Inr rules" 
  shows "get_TRS (ll_rules_to_wf_TRS rules) = R" 
  using assms
proof (transfer, goal_cases)
  case (1 R rules)
  from to_ll_rules_return[OF this]
  show ?case 
  proof (induct)
    case (Cons rule rules Rrule R)
    then show ?case using To_rule'[unfolded rel_fun_def, rule_format, of rule Rrule] by auto
  qed auto
qed

lemma mstep_rewrite_wf_ll_rules_to_wf_TRS: assumes "to_ll_rules R = Inr rules"
  shows "set (mstep_rewrite_wf (ll_rules_to_wf_TRS rules) t) = {u. (t,u) \<in> mstep (set R)}" 
proof -
  from is_OK_to_ll_rules[of R] assms have R: "left_lin_wf_trs (set R)" by auto
  note get_TRS = get_TRS_ll_rules_to_wf_TRS[OF assms]
  show ?thesis unfolding mstep_rewrite_wf_def get_TRS
  proof (rule set_mstep_rewrite_main)
    from R show "Trs.wf_trs (set R)" using wf_trs.wf_trs_alt[of "set R"]
      using left_lin_wf_trs_def by blast
  qed
qed

text \<open>main verified result: strong commutation via reachability\<close>
theorem automate_sim_cps_closed: 
  assumes Rr: "to_ll_rules R = return rules"
    and   Sr: "to_ll_rules S = return srules"
  shows "strongly_commute (mstep (set S)) (mstep (set R)) \<longleftrightarrow>
   (\<forall> s t vs. (s,t,vs) \<in> set (automate_sim_cps_closed ren rules srules) 
       \<longrightarrow> (\<exists> v \<in> set vs. (s,v) \<in> (rstep (set S))\<^sup>*))" 
proof -
  define list where "list = automate_sim_cps_closed ren rules srules"
  note list = list_def[unfolded automate_sim_cps_closed_def Let_def]
  from is_OK_to_ll_rules[of R] Rr have R: "left_lin_wf_trs (set R)" by auto
  from is_OK_to_ll_rules[of S] Sr have S: "left_lin_wf_trs (set S)" by auto
  let ?SCP = "Sim_cps_impl ren rules srules" 
  define scps where "scps = filter (\<lambda>pair. fst pair \<noteq> snd pair) ?SCP" 
  let ?mstep = "mstep_rewrite_wf (ll_rules_to_wf_TRS rules)" 
  from list[unfolded Rr Sr] 
  have list: "list = map (\<lambda>(s, t). (s, t, ?mstep t)) scps" 
    by (auto simp: scps_def)
  have mstep: "set (?mstep t) = {u. (t,u) \<in> mstep (set R)}" for t
    by (rule mstep_rewrite_wf_ll_rules_to_wf_TRS[OF Rr])
  define SCPs where "SCPs = (map_prod target target) ` ren.sim_cp ren (set R) (set S)" 
  define FSCPs where "FSCPs = Set.filter (\<lambda> p. fst p \<noteq> snd p) SCPs" 
  from ren_wf_trs.sim_cp_impl[of "set R" "set S" R S ren]
  have "set (sim_cp_impl ren R S) = ren.sim_cp ren (set R) (set S)" 
    by (metis R S ren_wf_trs.intro)
  hence "SCPs = set (sim_cps_impl ren R S)" 
    unfolding SCPs_def sim_cps_impl_def by auto
  also have "\<dots> = set ?SCP" 
    using to_ll_rules_return[OF Rr] to_ll_rules_return[OF Sr] Sim_cps_impl
    unfolding rel_fun_def by metis
  finally have FSCPs: "FSCPs = set scps" unfolding FSCPs_def scps_def by auto

  have "strongly_commute (mstep (set S)) (mstep (set R)) \<longleftrightarrow>
    (\<forall> s t. (s, t) \<in> SCPs \<longrightarrow>
           (\<exists>v. (s, v) \<in> (rstep (set S))\<^sup>* \<and> (t, v) \<in> mstep (set R)))"  
    unfolding strongly_commute_iff_sim_cps_joinable[OF R S, of ren] SCPs_def by auto
  also have "\<dots> \<longleftrightarrow> (\<forall> s t. (s, t) \<in> FSCPs \<longrightarrow>
           (\<exists>v. (s, v) \<in> (rstep (set S))\<^sup>* \<and> (t, v) \<in> mstep (set R)))" (is "?A = ?B")
  proof
    show "?A \<Longrightarrow> ?B" unfolding FSCPs_def by auto
    assume ?B
    show ?A
    proof (intro allI impI)
      fix s t
      assume "(s,t) \<in> SCPs" 
      from \<open>?B\<close>[rule_format, of s t] this
      show "\<exists>v. (s, v) \<in> (rstep (set S))\<^sup>* \<and> (t, v) \<in> mstep (set R)" 
        unfolding FSCPs_def by force
    qed
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall> s t. (s, t) \<in> set scps \<longrightarrow>
           (\<exists>v. (s, v) \<in> (rstep (set S))\<^sup>* \<and> (t, v) \<in> mstep (set R)))" 
    unfolding FSCPs by simp
  also have "\<dots> \<longleftrightarrow> (\<forall> s t vs. (s, t, vs) \<in> set list \<longrightarrow>
           (\<exists>v \<in> set vs. (s, v) \<in> (rstep (set S))\<^sup>*))" 
    unfolding list using mstep by force
  also have "\<dots> \<longleftrightarrow> (\<forall> s t vs. (s,t,vs) \<in> set (automate_sim_cps_closed ren rules srules) \<longrightarrow> 
           (\<exists> v \<in> set vs. (s,v) \<in> (rstep (set S))\<^sup>*))" 
    unfolding list_def ..
  finally show ?thesis .
qed 

(* a function that only works on terms of type string, where
   the verified renaming algorithm for string-literals has been fixed *)
definition "automate_sim_cps_closed_string_lit (R :: (String.literal,_)ll_rule list) S = 
  automate_sim_cps_closed string_lit_renameN R S " 

lemma automate_sim_cps_closed_string_lit: assumes   Rr: "to_ll_rules R = return rules"
  and Sr: "to_ll_rules S = return srules"
  shows "strongly_commute (mstep (set S)) (mstep (set R)) \<longleftrightarrow>
   (\<forall> s t vs. (s,t,vs) \<in> set (automate_sim_cps_closed_string_lit rules srules) 
       \<longrightarrow> (\<exists> v \<in> set vs. (s,v) \<in> (rstep (set S))\<^sup>*))" 
  unfolding automate_sim_cps_closed_string_lit_def
  by (rule automate_sim_cps_closed[OF assms])
 


subsection \<open>Algorithm for Reachability Search\<close>

text \<open>Below we write some algorithm to search for reachability 
  (given \<open>s\<close> and \<open>vs\<close>, search for \<open>\<exists> v \<in> set vs. (s,v) \<in> (rstep (set S))\<^sup>*\<close>)
   in a BFS-way\<close>

text \<open>Although several sub-algorithms have been verified, the assembling of the
  overall algorithm has not yet been verified.
  TODO: verification might be student project.\<close>

(* TODO: perhaps design a more-efficient version of \<open>rewrite\<close> that is also
  based on rule-maps *)

(* usage of \<open>the\<close> is fine, since we assumes wf_trs *)
definition tcap_impl where "tcap_impl rules = tcapRM2 (the (computeRuleMap rules))"

(* crude renaming, so that new names will not clash with proper symbol identifier;
   clashes would be harmless, since then the reach_necessary_criterion might just delete
   fewer non-reachable candidates *)
definition vars_to_const :: "(String.literal, String.literal) Term.term \<Rightarrow> (String.literal, String.literal) Term.term" 
  where "vars_to_const s = subst_apply_term s (\<lambda> x. Fun (STR ''_;_'' + x) [])" 

(* if s -R\<rightarrow>* t then reach_necessary_criterion R s t will evaluate to True *)
definition "reach_necessary_criterion R = (let tc = tcap_impl R 
    in (\<lambda> s t. Ground_Context.match (tc (vars_to_const s)) (vars_to_const t)))" 

datatype ('a,'b,'c)bfs_state = Found 'a | Search 'b | Fail 'c 

datatype ('f,'v)reach_info_state = Reach_Info_State "('f,'v)term set" "(('f,'v)term \<times> ('f,'v)term list)list" 
type_synonym ('f,'v)reach_cert = "('f,'v)term list" 
datatype ('f,'v)cp_reach_state = CP_Reach_State "('f, 'v)term" "('f, 'v)term" "('f, 'v)term set" 
    "('f, 'v)term list" "('f, 'v) reach_info_state"

datatype ('f,'v)cp_reach_cert = CP_Reach_Cert "('f,'v)term" "('f,'v)term" "('f,'v)reach_cert"

datatype ('f,'v)cp_search_state = CP_Search_State "('f,'v)term \<Rightarrow> ('f,'v)term list" "('f,'v)cp_reach_state list" "('f,'v)cp_reach_cert list" 

context
  fixes R :: "('f,'v)rules" 
    and reach_necc :: "('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool" 
begin

context 
  fixes rewr :: "('f,'v)term \<Rightarrow> ('f,'v)term list" 
begin

context
  fixes tgt :: "('f,'v)term set" 
    and tgtL :: "('f,'v)term list" 
begin
fun bfs_search_disj_step where
  "bfs_search_disj_step old new [] = Search (Reach_Info_State old new)" 
| "bfs_search_disj_step old new ((t,info) # todo) = (
    if t \<in> old then bfs_search_disj_step old new todo
    else if t \<in> tgt then Found info
    else let old' = insert t old in 
    if (\<exists> u \<in> set tgtL. reach_necc t u) then bfs_search_disj_step old' ((t,info) # new) todo
    else bfs_search_disj_step old' new todo)"

fun bfs_search_single_disj :: "('f,'v)reach_info_state \<Rightarrow> (('f,'v)reach_cert,('f,'v)reach_info_state,unit)bfs_state" 
    where "bfs_search_single_disj (Reach_Info_State old todos) = (if todos = [] then Fail ()
   else bfs_search_disj_step old [] (List.maps (\<lambda> (t,info). map (\<lambda> u. (u,u # info)) (rewr t)) todos))"
end

fun create_cp_cert_rev where 
  "create_cp_cert_rev s t [] = CP_Reach_Cert s t []"
| "create_cp_cert_rev s t (u # info) = (if u = s then create_cp_cert_rev s t info
    else CP_Reach_Cert s t (u # info))"

(* for the certificates, we need to reverse the list, and we prune leading s and
  trailing t, since these elements are implicit in CPF3 *)
fun create_cp_cert where 
  "create_cp_cert s t [] = CP_Reach_Cert s t []"
| "create_cp_cert s t (u # info) = (if u = t then create_cp_cert s t info
    else create_cp_cert_rev s t (rev (u # info)))"

fun bfs_search_conj_main where
  "bfs_search_conj_main done [] [] = Found done"
| "bfs_search_conj_main done ctd [] = Search (CP_Search_State (rewrite R) ctd done)"
| "bfs_search_conj_main done ctd (CP_Reach_State s t tgt tgtL ris # todo) = (case bfs_search_single_disj tgt tgtL ris of
      Found info \<Rightarrow> bfs_search_conj_main (create_cp_cert s t info # done) ctd todo
    | Fail _ \<Rightarrow> Fail (s,t)
    | Search next \<Rightarrow> bfs_search_conj_main done (CP_Reach_State s t tgt tgtL next # ctd) todo)"
end

fun bfs_search_conj_step :: "('f,'v)cp_search_state
     \<Rightarrow> (('f, 'v) cp_reach_cert list, ('f,'v)cp_search_state, ('f,'v)rule) bfs_state" where
  "bfs_search_conj_step (CP_Search_State rewr ctd done) = bfs_search_conj_main rewr done [] ctd" 

fun init_state_main where 
  "init_state_main cps_set ((s,t,vs) # cps) = (
     if (s,t) \<in> cps_set then init_state_main cps_set cps
     else CP_Reach_State s t (set vs) vs (Reach_Info_State {} [(s,[])]) 
         # init_state_main (insert (s,t) cps_set) cps)" 
| "init_state_main cps_set [] = []" 

definition init_state :: "_ \<Rightarrow> (('f, 'v) Term.term \<times> ('f, 'v) Term.term \<times> ('f, 'v) Term.term list) list \<Rightarrow> ('f, 'v) cp_search_state" where
  "init_state init_rewr cps = CP_Search_State init_rewr (init_state_main {} cps) []"
end

(* this solver uses first a multistep, and requires a well-formed left-linear TRS *)
definition bfs_solver where
  "bfs_solver S Sll = (let 
    SS = ll_rules_to_wf_TRS Sll;
    init_rewr = mstep_rewrite_wf SS;
    init = init_state init_rewr;
    step = bfs_search_conj_step S (reach_necessary_criterion S)
   in (init,step))" 

(* this solver uses first an optional step, and assumes a well-formed TRS *)
definition bfs_solver_generic where
  "bfs_solver_generic S = (let
    init_rewr = (\<lambda> t. t # rewrite S t);
    init = init_state init_rewr;
    step = bfs_search_conj_step S (reach_necessary_criterion S)
  in (init, step))" 

text \<open>The function \<open>iterative_comm_solver\<close> is the main search algorithm: 
  gives two TRSs, it is first checked that
  they are well-formed and left-linear, and if a pair is returned (s,step) is
  returned:  
  \<^item> s is the initial search state (encoding the reachability problem for Okui's criterion)
  \<^item> step is a function that converts a state into either 
     success with a certificate,
     fail,
     or a new state (where further possibilities have been explored)
    \<close>
definition iterative_comm_solver where
  "iterative_comm_solver R S = do {
       RR \<leftarrow> to_ll_rules R;
       SS \<leftarrow> to_ll_rules S;
       let cps = automate_sim_cps_closed_string_lit RR SS;
       case bfs_solver S SS of (init, step) \<Rightarrow> return (init cps, step)
    }" 
  

text \<open>The function \<open>iterative_reach_solver\<close> is the main search algorithm for reachability: 
  given a well-formed TRS and a list of conditions s = t,
  a pair (state,step) is returned:  
  \<^item> state is the initial search state (encoding the reachability problem s ->* t for all conditions)
  \<^item> step is a function that converts a state into either 
     success with a certificate,
     fail,
     or a new state (where further possibilities have been explored)
  \<^item> note that the order of conditions s = t in the generated certificates (s, t, [intermediate terms])
       does not necessarily reflect the order of the original condition list
    \<close>
definition iterative_reach_solver where
  "iterative_reach_solver R (conds :: (_,String.literal)rule list) = (
       let prob = map (\<lambda> (s,t). (s, t, [t])) conds in
       case bfs_solver_generic R of (init, step) \<Rightarrow> (init prob, step)
    )" 

fun root_rewr :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> (('f,'v)rule \<times> ('v \<times> ('f,'v)term) list)option" where
  "root_rewr [] s t = None" 
| "root_rewr ((l,r) # trs) s t = (case Matching.match_list Var [(l,s),(r,t)] of
     None \<Rightarrow> root_rewr trs s t 
   | Some \<sigma> \<Rightarrow> Some ((l,r), map (\<lambda> x. (x, \<sigma> x)) (remdups (vars_term_list l))))" 

(* given two different terms s and t such that s \<rightarrow> t, this algorithm reconstructs 
   some possible position, rule and substitution from the rewrite step;
   the algorithm crashes if s \<rightarrow> t does not hold or if s = t *)
(* TODO: one might want to prove soundness, e.g., ITP-course exercise/project *)
fun rewr_reconstruct :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> pos \<times> ('f,'v)rule \<times> ('v \<times> ('f,'v)term)list" 
  and rewr_reconstruct_list where
  "rewr_reconstruct trs s t = (case root_rewr trs s t of Some (lr,sig) \<Rightarrow> ([], lr, sig)
     | None \<Rightarrow> (case (s,t) of (Fun f ss, Fun g ts) \<Rightarrow> rewr_reconstruct_list trs 0 ss ts))" 
| "rewr_reconstruct_list trs i (s # ss) (t # ts) = (if s = t then rewr_reconstruct_list trs (i + 1) ss ts
     else (case rewr_reconstruct trs s t of (p,lr,sig) \<Rightarrow> (i # p, lr,sig)))" 

definition "rewr_reconstruct_pos_from_1 trs s t = map_prod (map (integer_of_nat o Suc)) id (rewr_reconstruct trs s t)" 
end