theory LP_Cut_SEG_Triple_Answers
  imports LP_Dependency_Triple_Models LP_Cut_SEG_Triple_Contracts
    LP_Cut_Return_Interface_Lift LP_Cut_SEG_Free_Control
begin

definition lpc_triple_answer_contract where
  "lpc_triple_answer_contract P ss Q ret =
    (SN_on (lp_cut_mgu_source P) {map fst ss} \<and>
      (\<forall>eta. lpc_actual_return P ss eta \<longrightarrow> lp_answer_model Q (ret eta)))"

lemma lpc_triple_answer_contract_SN:
  "lpc_triple_answer_contract P ss Q ret \<Longrightarrow>
    SN_on (lp_cut_mgu_source P) {map fst ss}"
  by (simp add: lpc_triple_answer_contract_def)

lemma lpc_triple_answer_contract_return:
  "lpc_triple_answer_contract P ss Q ret \<Longrightarrow>
    lpc_actual_return P ss eta \<Longrightarrow> lp_answer_model Q (ret eta)"
  by (simp add: lpc_triple_answer_contract_def)

lemma lpc_triple_answer_contract_covered:
  "lpc_triple_answer_contract P ss Q ret \<Longrightarrow>
    lpc_answers_covered P ss (\<lambda>eta. lp_answer_model Q (ret eta))"
  by (auto simp: lpc_triple_answer_contract_def lpc_answers_covered_def lpc_actual_return_def)

definition lpc_answer_model_relation where
  "lpc_answer_model_relation Q = {(None,Some a) |a. lp_answer_model Q a}"

lemma lpc_answer_model_relation_path:
  "(None,Some a)\<in>(lpc_answer_model_relation Q)\<^sup>* \<longleftrightarrow> lp_answer_model Q a"
proof
  assume path: "(None,Some a)\<in>(lpc_answer_model_relation Q)\<^sup>*"
  have "b=None \<or> (\<exists>a. b=Some a \<and> lp_answer_model Q a)"
    if "(None,b)\<in>(lpc_answer_model_relation Q)\<^sup>*" for b
    using that by (induct rule: rtrancl_induct)
      (auto simp: lpc_answer_model_relation_def)
  then show "lp_answer_model Q a" using path by auto
next
  assume "lp_answer_model Q a"
  then have "(None,Some a)\<in>lpc_answer_model_relation Q"
    by (cases a) (auto simp: lpc_answer_model_relation_def)
  then show "(None,Some a)\<in>(lpc_answer_model_relation Q)\<^sup>*" by auto
qed

lemma lpc_triple_answer_contract_return_contract:
  "lpc_triple_answer_contract P ss Q ret \<longleftrightarrow>
    lpc_return_contract P ss (lpc_answer_model_relation Q) None (\<lambda>eta. Some (ret eta))"
  by (auto simp: lpc_triple_answer_contract_def lpc_return_contract_def
    lpc_actual_return_def lpc_answer_model_relation_path)

theorem lpc_triple_answer_control:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_seg_free_check_control fuel P C nds states Fs returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of C"
    and program: "lp_cut_source_program P"
    and represented: "lpc_return_free_module_rep nds states Fs ss a"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      (a,[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild C)\<^sup>* \<Longrightarrow>
      lpc_triple_answer_contract P (lpc_return_eval eta (states!i)) Q ret"
    and emit: "\<And>rho. (a,[(returned,map rho [0..<arity])])\<in>(lp_ild C)\<^sup>* \<Longrightarrow>
      lp_answer_model Q (ret rho)"
  shows "lpc_triple_answer_contract P ss Q ret"
  unfolding lpc_triple_answer_contract_return_contract
  by (rule lpc_seg_free_control_contract[OF checked ranked program represented])
    (auto intro: boundary emit simp: lpc_triple_answer_contract_return_contract[symmetric]
      lpc_answer_model_relation_path)

theorem lpc_triple_answer_contract_modular:
  assumes descent: "SN_on D {a}"
    and represented: "rep ss a ret"
    and local: "\<And>us b out. rep us b out \<Longrightarrow>
      (\<And>vs c final. (b,c)\<in>D \<Longrightarrow> rep vs c final \<Longrightarrow>
        lpc_triple_answer_contract P vs Q final) \<Longrightarrow>
      lpc_triple_answer_contract P us Q out"
  shows "lpc_triple_answer_contract P ss Q ret"
proof -
  have all: "\<forall>us out. rep us b out \<longrightarrow> lpc_triple_answer_contract P us Q out"
    if sn: "SN_on D {b}" for b
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix b us out
    assume ih: "\<And>c. (b,c)\<in>D \<Longrightarrow>
      \<forall>vs final. rep vs c final \<longrightarrow> lpc_triple_answer_contract P vs Q final"
      and rep: "rep us b out"
    show "lpc_triple_answer_contract P us Q out"
      by (rule local[OF rep]) (use ih in blast)
  qed
  show ?thesis using all[OF descent] represented by blast
qed

text \<open>Recover the caller's complete observation from a checked child
interface. The bridge need only hold for successful child answers. It may use
a supporting clause, including extra variables not occurring in that child.\<close>

theorem lpc_triple_answer_lift_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpc_triple_answer_contract P (lpc_reinterface F ss) Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret (F eta)) \<Longrightarrow>
      lp_answer_model Q (final eta)"
  shows "lpc_triple_answer_contract P ss Q final"
proof (unfold lpc_triple_answer_contract_def, intro conjI allI impI)
  show "SN_on (lp_cut_mgu_source P) {map fst ss}"
    using lpc_triple_answer_contract_SN[OF contract] by simp
next
  fix eta assume actual: "lpc_actual_return P ss eta"
  obtain us tail where path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some eta) tail"
    using actual by (auto simp: lpc_actual_return_def)
  have reached: "(lpc_reinterface F ss,lpc_reinterface F us)\<in>(lpc_answer_steps P)\<^sup>*"
    by (rule lpc_reinterface_path_forward[where F=F, OF commute path])
  have emitted: "lpc_answer_transition P (lpc_reinterface F us) (Some (F eta)) (lpc_reinterface F tail)"
    using lpc_reinterface_forward[where F=F, OF commute event] by simp
  have child: "lpc_actual_return P (lpc_reinterface F ss) (F eta)"
    using reached emitted by (auto simp: lpc_actual_return_def)
  show "lp_answer_model Q (final eta)"
    by (rule bridge[OF lpc_triple_answer_contract_return[OF contract child]])
qed

theorem lpc_triple_answer_project_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpc_triple_answer_contract P ss Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret eta) \<Longrightarrow>
      lp_answer_model Q (final (F eta))"
  shows "lpc_triple_answer_contract P (lpc_reinterface F ss) Q final"
proof (unfold lpc_triple_answer_contract_def, intro conjI allI impI)
  show "SN_on (lp_cut_mgu_source P) {map fst (lpc_reinterface F ss)}"
    using lpc_triple_answer_contract_SN[OF contract] by simp
next
  fix rho assume actual: "lpc_actual_return P (lpc_reinterface F ss) rho"
  obtain us tail where path: "(lpc_reinterface F ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some rho) tail"
    using actual by (auto simp: lpc_actual_return_def)
  obtain vs where reached: "(ss,vs)\<in>(lpc_answer_steps P)\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpc_reinterface_path_reflect[OF commute path] by blast
  have event': "lpc_answer_transition P (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where step: "lpc_answer_transition P vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using lpc_reinterface_reflect[OF commute event'] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have source: "lpc_actual_return P ss eta"
    using reached step ev by (auto simp: lpc_actual_return_def)
  show "lp_answer_model Q (final rho)"
    unfolding rho by (rule bridge[OF lpc_triple_answer_contract_return[OF contract source]])
qed

theorem lpc_triple_answer_boundary:
  assumes child_commute: "\<And>eta sigma. G (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (G eta y) sigma)"
    and parent_commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and child: "lpc_triple_answer_contract P (lpc_reinterface G ss) Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret (G eta)) \<Longrightarrow>
      lp_answer_model Q (final (F eta))"
  shows "lpc_triple_answer_contract P (lpc_reinterface F ss) Q final"
proof -
  have full: "lpc_triple_answer_contract P ss Q (\<lambda>eta. final (F eta))"
    by (rule lpc_triple_answer_lift_interface[OF child_commute child bridge])
  show ?thesis by (rule lpc_triple_answer_project_interface[OF parent_commute full]) simp
qed

theorem lpc_triple_answer_split:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and prefix: "lpc_triple_answer_contract P ss Q ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. lpc_actual_return P ss eta \<Longrightarrow>
      lp_answer_model Q (ret eta) \<Longrightarrow>
      lpc_triple_answer_contract P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q final"
  shows "lpc_triple_answer_contract P (lpc_attach_answers rest ss) Q final"
proof -
  have plain: "lpc_return_contract P ss (UNIV::unit rel) () (\<lambda>_. ())"
    using lpc_triple_answer_contract_SN[OF prefix]
    by (auto simp: lpc_return_contract_def)
  have child: "lpc_triple_answer_contract P
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q final"
    if actual: "lpc_actual_return P ss eta" for eta
    by (rule continuation[OF actual lpc_triple_answer_contract_return[OF prefix actual]])
  have child_sn: "SN_on (lp_cut_mgu_source P)
    {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest)]}"
    if actual: "lpc_actual_return P ss eta" for eta
    using lpc_triple_answer_contract_SN[OF child[OF actual]] by simp
  have sn: "SN_on (lp_cut_mgu_source P) {lpc_attach rest ss}"
    by (rule lpc_return_source_SN_actual[OF program plain valid separated child_sn])
  have answers: "lpc_answers_covered P (lpc_attach_answers rest ss)
    (\<lambda>eta. lp_answer_model Q (final eta))"
  proof (rule lpc_attach_answers_covered_actual[OF program plain valid separated])
    fix eta assume actual: "lpc_actual_return P ss eta"
    show "SN_on (lp_cut_mgu_source P)
      {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest)]}"
      by (rule child_sn[OF actual])
  next
    fix eta assume actual: "lpc_actual_return P ss eta"
    show "lpc_answers_covered P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)]
      (\<lambda>eta. lp_answer_model Q (final eta))"
      by (rule lpc_triple_answer_contract_covered[OF child[OF actual]])
  qed
  show ?thesis using sn answers
    by (auto simp: lpc_triple_answer_contract_def lpc_answers_covered_def
      lpc_actual_return_def lpc_attach_answers_erases)
qed

end
