theory LP_Cut_Return_Free_Resolution
  imports LP_Cut_Return_Free_Link LP_Cut_Return_Table_Resolution LP_Cut_MGU_Resolution LP_Cut_Joint_Free_Check
begin

definition lpc_return_context_free where
  "lpc_return_context_free F G a gs k =
    (if vars_term a \<subseteq> set G\<union>set F then
      filter (\<lambda>x. x\<notin>vars_term a \<and> x\<notin>set G \<and> length x<k \<and>
        list_ex (\<lambda>g. list_ex (\<lambda>t. x\<in>vars_term t) (lp_cut_terms g)) gs) F else [])"

definition lpc_return_resolution_free_fallback where
  "lpc_return_resolution_free_fallback F G a gs h bs k l =
    (let result=lpc_mgu_result_free F G a h (LPCAtom h#bs) l in
      if result=[] then (let ctx=lpc_return_context_free F G a gs k in
        if ctx=[] then filter (\<lambda>x. length x<k) F else map (lp_prefix k) ctx) else result)"

lemma lpc_return_resolution_free_fallback_sound:
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and free: "lpc_free_knowledge (set F) eta"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and bounds: "2 * k \<le> l"
  shows "lpc_free_knowledge (set (lpc_return_resolution_free_fallback F G a gs h bs k l))
    (lp_cut_resolution_env k l eta sigma rho)"
proof (cases "lpc_mgu_result_free F G a h (LPCAtom h#bs) l=[]")
  case False
  show ?thesis using lpc_mgu_result_free_sound[OF lpc_mgu_head_observation[OF mgu] free ground] False
    by (simp add: lpc_return_resolution_free_fallback_def)
next
  case True
  note no_body=True
  let ?C="lpc_return_context_free F G a gs k"
  show ?thesis
  proof (cases "?C=[]")
    case True
    show ?thesis using free bounds True no_body
      by (auto simp: lpc_return_resolution_free_fallback_def lpc_free_knowledge_def lp_cut_resolution_env_def inj_on_def)
  next
    case False
    have vars: "vars_term a \<subseteq> set G\<union>set F" using False by (auto simp: lpc_return_context_free_def split: if_splits)
    have subset: "set ?C \<subseteq> set F" and disjoint: "set ?C \<inter> vars_term a = {}"
      and occurs: "set ?C \<subseteq> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
      by (auto simp: lpc_return_context_free_def list_ex_iff)
    have context_free: "lpc_free_knowledge (set ?C) (\<lambda>x. lp_isubst (eta x) sigma)"
      by (rule lpc_mgu_untouched_context_free[OF mgu free ground vars subset disjoint occurs])
    have env: "lp_cut_resolution_env k l eta sigma rho (lp_prefix k x)=lp_isubst (eta x) sigma" if x: "x\<in>set ?C" for x
    proof -
      have short: "length x<k" using x by (auto simp: lpc_return_context_free_def)
      have upper: "k+length x<l" using short bounds by arith
      have not_upper: "\<not> l \<le> k + length x" using upper by arith
      show ?thesis by (simp add: lp_cut_resolution_env_def lp_prefix_def not_upper)
    qed
    show ?thesis using context_free env False no_body
      by (auto simp: lpc_return_resolution_free_fallback_def lpc_free_knowledge_def inj_on_def)
  qed
qed

definition lpc_return_resolution_free_uniform where
  "lpc_return_resolution_free_uniform fuel F G a gs h bs k l =
    (let prefix=Suc (fold max (map length (vars_term_list a)) 0);
         C=lpc_uniform_free_outputs fuel prefix G F a h bs in
      if C=[] then lpc_return_resolution_free_fallback F G a gs h bs k l
      else map (lp_prefix l) C)"

lemma lpc_return_resolution_free_uniform_sound:
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and free: "lpc_free_knowledge (set F) eta"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and bounds: "2 * k \<le> l"
  shows "lpc_free_knowledge (set (lpc_return_resolution_free_uniform fuel F G a gs h bs k l))
    (lp_cut_resolution_env k l eta sigma rho)"
proof -
  let ?p="Suc (fold max (map length (vars_term_list a)) 0)"
  let ?C="lpc_uniform_free_outputs fuel ?p G F a h bs"
  have known: "lpc_free_knowledge (set ?C) rho"
    by (rule lpc_uniform_free_outputs_sound[OF mgu ground free])
  have fallback: "lpc_free_knowledge (set (lpc_return_resolution_free_fallback F G a gs h bs k l))
    (lp_cut_resolution_env k l eta sigma rho)"
    by (rule lpc_return_resolution_free_fallback_sound[OF mgu free ground bounds])
  have env: "\<And>x. lp_cut_resolution_env k l eta sigma rho (lp_prefix l x)=rho x"
    by (simp add: lp_cut_resolution_env_def lp_prefix_def)
  show ?thesis using known fallback
    by (auto simp: lpc_return_resolution_free_uniform_def Let_def lpc_free_knowledge_def inj_on_def env)
qed

definition lpc_return_resolution_free where
  "lpc_return_resolution_free fuel F G a gs h bs k l =
    (let C=lpc_joint_resolution_free fuel F G a gs h bs k l in
      if C=[] then lpc_return_resolution_free_uniform fuel F G a gs h bs k l else C)"

lemma lpc_return_resolution_free_sound:
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and free: "lpc_free_knowledge (set F) eta"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and bounds: "2 * k \<le> l"
  shows "lpc_free_knowledge (set (lpc_return_resolution_free fuel F G a gs h bs k l))
    (lp_cut_resolution_env k l eta sigma rho)"
  using lpc_joint_resolution_free_sound[OF mgu ground free bounds]
    lpc_return_resolution_free_uniform_sound[OF mgu free ground bounds]
  by (simp add: lpc_return_resolution_free_def Let_def)

definition lpc_return_free_resolution_base where
  "lpc_return_free_resolution_base fuel P Q nds Fs nd F a gs c m es k l A next anchors bindings mode yes no =
    (c<length P \<and> lpcn_state nd=LPCClause (LPCAtom a#gs) c m#es \<and>
     (lp_cut_check_coverage fuel k a (fst (P!c)) bindings mode \<or>
      (mode=LPCAlwaysSuccess \<and> (lpc_check_free_call F a (fst (P!c)) \<or>
        lpc_check_mixed_free_call fuel k (lpcn_ground nd) F a (fst (P!c))))) \<and>
     (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
       lp_cut_check_resolution P fuel k l (lpcn_ground nd) A (lpcn_guards nd) a gs c m es next anchors \<and>
       (\<forall>x\<in>set (lpcn_vars nd). length x<k)))"

definition lpc_check_return_free_resolution_node where
  "lpc_check_return_free_resolution_node fuel P Q nds states Fs nd F a gs c m active saved k l A next anchors bindings mode outputs yes no =
    (lpc_return_free_resolution_base fuel P Q nds Fs nd F a gs c m (map fst saved) k l A next anchors bindings mode yes no \<and>
     (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
       lpc_return_short k saved \<and>
       lpc_check_return_values fuel k (lpcn_ground nd)
         (lp_cut_resolution_equations k l (lpcn_ground nd) a (fst (P!c)))
         active (concat (map snd saved)) outputs \<and>
       lpc_check_return_free_table_link fuel Q nds states Fs nd ((LPCGoals next,outputs)#saved)
         (lpcn_ground nd@sorted_list_of_set (lp_cut_anchor_vars anchors))
         (lpcn_guards nd@lpc_negative_guards k (set (lpcn_ground nd)) (lpcn_guards nd)@[LPCHeadGuard a (fst (P!c)) True])
         (lp_cut_resolution_equations k l (lpcn_ground nd) a (fst (P!c)))
         (lpc_return_resolution_free fuel F (lpcn_ground nd) a gs (fst (P!c)) (snd (P!c)) k l) yes) \<and>
     (mode\<noteq>LPCAlwaysSuccess \<longrightarrow>
       lpc_check_return_free_table_link fuel Q nds states Fs nd saved (lpcn_ground nd)
         (lpcn_guards nd@[LPCHeadGuard a (fst (P!c)) False]) [] F no))"

theorem lpc_return_free_resolution_node_sound:
  assumes checked: "lpc_check_return_free_resolution_node fuel P Q nds states Fs nd F a gs c m active saved k l A next anchors bindings mode outputs yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpc_return_free_rep nds states Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?a = "lp_ieval a eta"
  let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  let ?saved = "lpc_return_eval eta saved"
  let ?ret = "lpc_return_env active eta"
  have base: "lpc_return_free_resolution_base fuel P Q nds Fs nd F a gs c m (map fst saved) k l A next anchors bindings mode yes no"
    using checked by (simp add: lpc_check_return_free_resolution_node_def)
  have coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) bindings mode \<or>
    (mode=LPCAlwaysSuccess \<and> (lpc_check_free_call F a (fst (P!c)) \<or>
       lpc_check_mixed_free_call fuel k ?G F a (fst (P!c))))"
    using base by (simp add: lpc_return_free_resolution_base_def)
  have st: "lpc_answer_transition P ((LPCClause (LPCAtom ?a#?gs) c m,?ret)#?saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have cases: "(\<exists>sigma rho.
      lpc_mgu_resolve ?a ?gs (fst (P!c)) (snd (P!c)) sigma rho \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved) \<or>
    (event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm. \<exists>rho.
        lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho))"
    using st by (cases rule: lpc_answer_transition.cases) auto
  from cases show ?thesis
  proof
    assume "\<exists>sigma rho. lpc_mgu_resolve ?a ?gs (fst (P!c)) (snd (P!c)) sigma rho \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs), (\<lambda>n. lp_isubst (?ret n) sigma))#?saved"
    then obtain sigma rho where mgu: "lpc_mgu_resolve ?a ?gs (fst (P!c)) (snd (P!c)) sigma rho"
      and event: "event=None" and result: "tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs), (\<lambda>n. lp_isubst (?ret n) sigma))#?saved" by blast
    have eq: "lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho"
      using mgu by (simp add: lpc_mgu_resolve_def)
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using coverage lp_cut_coverage_failure[of fuel k a "fst (P!c)" bindings mode] eq by auto
    have resolve: "lp_cut_check_resolution P fuel k l ?G A ?K a gs c m (map fst saved) next anchors"
      and parent: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      using base possible by (auto simp: lpc_return_free_resolution_base_def)
    have payload: "lpc_check_return_values fuel k ?G (lp_cut_resolution_equations k l ?G a (fst (P!c)))
      active (concat (map snd saved)) outputs"
      and short: "lpc_return_short k saved"
      and link: "lpc_check_return_free_table_link fuel Q nds states Fs nd ((LPCGoals next,outputs)#saved)
        (?G@sorted_list_of_set (lp_cut_anchor_vars anchors))
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True])
        (lp_cut_resolution_equations k l ?G a (fst (P!c)))
        (lpc_return_resolution_free fuel F ?G a gs (fst (P!c)) (snd (P!c)) k l) yes"
      using checked possible by (auto simp: lpc_check_return_free_resolution_node_def)
    let ?env = "lp_cut_resolution_env k l eta sigma rho"
    have same: "tt=lpc_return_eval ?env ((LPCGoals next,outputs)#saved)"
      using result lpc_return_resolution_success[OF resolve known eq payload short]
      by (simp add: map_map o_def lp_cut_map_comp)
    have equations: "lp_equations (lp_cut_resolution_equations k l ?G a (fst (P!c))) ?env"
      by (rule lp_cut_checked_resolution_equations[OF resolve known eq])
    have kl: "k\<le>l" using resolve by (auto simp: lp_cut_check_resolution_def)
    have old: "map ?env (lpcn_vars nd)=map eta (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl parent])
    have prior: "lp_cut_knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using lp_cut_check_resolution_success(2)[OF resolve known eq]
      by (simp add: lp_cut_anchor_vars_def)
    have negative: "list_all (\<lambda>g. lp_cut_guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule lpc_negative_guards_sound[OF _ _ known])
        (use resolve in \<open>auto simp: lp_cut_check_resolution_def\<close>)
    have knowledge: "lp_cut_knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using prior negative by (simp add: lp_cut_knowledge_def)
    have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
      using known by (simp add: lp_cut_knowledge_def)
    have bounds: "2 * k \<le> l" using resolve by (simp add: lp_cut_check_resolution_def)
    have body_free: "lpc_free_knowledge (set (lpc_return_resolution_free fuel F ?G a gs (fst (P!c)) (snd (P!c)) k l)) ?env"
      by (rule lpc_return_resolution_free_sound[OF mgu free ground bounds])
    show ?thesis using lpc_return_free_table_link_sound[OF link equations old knowledge body_free] event same by simp
  next
    assume failure: "event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm. \<exists>rho.
        lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
    proof
      assume success: "mode=LPCAlwaysSuccess"
      have "\<exists>sigma rho :: string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm.
        lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho"
      proof (cases "lp_cut_check_coverage fuel k a (fst (P!c)) bindings mode")
        case True then show ?thesis using lp_cut_coverage_success[OF True] success by blast
      next
        case False
        then have "lpc_check_free_call F a (fst (P!c)) \<or>
          lpc_check_mixed_free_call fuel k ?G F a (fst (P!c))" using coverage by blast
        then show ?thesis
        proof
          assume "lpc_check_free_call F a (fst (P!c))"
          then show ?thesis by (rule lpc_check_free_call_sound[OF _ free])
        next
          assume mixed: "lpc_check_mixed_free_call fuel k ?G F a (fst (P!c))"
          have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
            using known by (simp add: lp_cut_knowledge_def)
          show ?thesis by (rule lpc_check_mixed_free_call_sound[OF mixed ground free])
        qed
      qed
      then show False using failure by blast
    qed
    have link: "lpc_check_return_free_table_link fuel Q nds states Fs nd saved ?G
      (?K@[LPCHeadGuard a (fst (P!c)) False]) [] F no"
      using checked possible by (simp add: lpc_check_return_free_resolution_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCHeadGuard a (fst (P!c)) False]) eta"
      using known failure by (simp add: lp_cut_knowledge_def)
    show ?thesis using lpc_return_free_table_link_sound[OF link _ refl knowledge free] failure
      by (simp add: lp_equations_def)
  qed
qed

end
