theory LP_Prolog_Stopped_Return_Interface
  imports LP_Prolog_Stopped_Answers LP_Prolog_Return_Interface LP_Prolog_Triple_Interface
begin

lemma lpp_stopped_reinterface_empty:
  "lpc_reinterface F ss=[] \<longleftrightarrow> ss=[]"
  by (simp add: lpc_reinterface_def)

lemma lpp_stopped_reinterface_nil:
  "lpc_reinterface F []=[]"
  by (simp add: lpc_reinterface_def)

lemma lpp_undefined_stop_reinterface:
  "lpp_undefined_answer_stop P B (lpc_reinterface F ss) = lpp_undefined_answer_stop P B ss"
  by (simp add: lpp_undefined_answer_stop_def)

lemma lpp_stopped_reinterface_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) ss event tt"
  shows "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (lpc_reinterface F ss) (map_option F event) (lpc_reinterface F tt)"
  using step lpp_domain_reinterface_forward[where F=F, OF commute]
  by (auto simp: lp_answer_stop_def lpp_undefined_stop_reinterface lpp_stopped_reinterface_empty lpp_stopped_reinterface_nil split: if_splits)

lemma lpp_stopped_reinterface_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (lpc_reinterface F ss) event tt"
  shows "\<exists>ev us. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) ss ev us \<and>
    map_option F ev=event \<and> lpc_reinterface F us=tt"
proof (cases "lpp_undefined_answer_stop P B ss")
  case True
  have facts: "ss\<noteq>[]" "event=None" "tt=[]"
    using step True by (auto simp: lp_answer_stop_def lpp_undefined_stop_reinterface lpp_stopped_reinterface_empty lpp_stopped_reinterface_nil)
  show ?thesis by (intro exI[of _ None] exI[of _ "[]"])
    (use True facts in \<open>simp add: lp_answer_stop_def lpp_stopped_reinterface_empty lpp_stopped_reinterface_nil\<close>)
next
  case False
  have nonempty: "ss\<noteq>[]" and original: "lpp_domain_answers P B U D (lpc_reinterface F ss) event tt"
    using step False by (auto simp: lp_answer_stop_def lpp_undefined_stop_reinterface lpp_stopped_reinterface_empty lpp_stopped_reinterface_nil)
  show ?thesis using lpp_domain_reinterface_reflect[where F=F, OF commute original] False nonempty
    by (auto simp: lp_answer_stop_def)
qed

lemma lpp_stopped_contract_project:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss R t ret"
    and bridge: "\<And>eta. (ret eta,final (F eta))\<in>R\<^sup>*"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) (lpc_reinterface F ss) R t final"
proof (rule lp_answer_contract_simulation[where rep="\<lambda>us vs. lpc_reinterface F us = vs"
    and outputs="\<lambda>a b. b = F a", OF contract refl])
  fix us vs event ws
  assume shape: "lpc_reinterface F us = vs" and step: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) vs event ws"
  obtain ev zs where local: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us ev zs"
    and out: "map_option F ev = event" and target: "lpc_reinterface F zs = ws"
    using lpp_stopped_reinterface_reflect[where F=F, OF commute, of P B U D us event ws] step shape by blast
  show "\<exists>ev zs. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us ev zs \<and> lpc_reinterface F zs = ws \<and>
    (\<forall>beta. event = Some beta \<longrightarrow> (\<exists>alpha. ev = Some alpha \<and> beta = F alpha))"
    using local out target by (cases ev) auto
qed (use bridge in auto)

lemma lpp_stopped_contract_lift_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) (lpc_reinterface F ss) R t ret"
    and bridge: "\<And>eta. (ret (F eta),final eta)\<in>R\<^sup>*"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss R t final"
proof (rule lp_answer_contract_simulation[where rep="\<lambda>us vs. us = lpc_reinterface F vs"
    and outputs="\<lambda>a b. a = F b", OF contract refl])
  fix us vs event ws
  assume shape: "us = lpc_reinterface F vs" and step: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) vs event ws"
  have local: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us (map_option F event) (lpc_reinterface F ws)"
    using lpp_stopped_reinterface_forward[where F=F, OF commute step] shape by simp
  show "\<exists>ev zs. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us ev zs \<and> zs = lpc_reinterface F ws \<and>
    (\<forall>beta. event = Some beta \<longrightarrow> (\<exists>alpha. ev = Some alpha \<and> alpha = F beta))"
    by (intro exI[of _ "map_option F event"] exI[of _ "lpc_reinterface F ws"])
      (use local in auto)
qed (use bridge in auto)
lemma lpp_stopped_reinterface_path_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and path: "(ss,tt)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)))\<^sup>*"
  shows "(lpc_reinterface F ss,lpc_reinterface F tt)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)))\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step tt uu)
  obtain event where event: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) tt event uu"
    using step by (auto simp: lp_answer_steps_def)
  have edge: "(lpc_reinterface F tt,lpc_reinterface F uu)\<in>lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))"
    using lpp_stopped_reinterface_forward[where F=F, OF commute event] by (auto simp: lp_answer_steps_def)
  show ?case using step edge by (blast intro: rtrancl_into_rtrancl)
qed


lemma lpp_stopped_reinterface_path_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and path: "(lpc_reinterface F ss,tt)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)))\<^sup>*"
  shows "\<exists>us. (ss,us)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)))\<^sup>* \<and> lpc_reinterface F us=tt"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by auto
next
  case (step tt uu)
  obtain us where reached: "(ss,us)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)))\<^sup>*"
    and shape: "lpc_reinterface F us=tt" using step by blast
  obtain event where event: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (lpc_reinterface F us) event uu"
    using step shape by (auto simp: lp_answer_steps_def)
  obtain ev vs where local: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us ev vs"
    and out: "lpc_reinterface F vs=uu"
    using lpp_stopped_reinterface_reflect[OF commute event] by blast
  have edge: "(us,vs)\<in>lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))" using local by (auto simp: lp_answer_steps_def)
  have "(ss,vs)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)))\<^sup>*" by (rule rtrancl_into_rtrancl[OF reached edge])
  then show ?case using out by blast
qed


lemma lpp_stopped_reinterface_SN:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
  shows "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))) {lpc_reinterface F ss} =
    SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))) {ss}"
proof
  assume sn: "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))) {lpc_reinterface F ss}"
  have contract: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) (lpc_reinterface F ss) ({}::bool rel) False (\<lambda>_. False)"
    using sn by (auto simp: lp_answer_contract_def lp_answers_covered_def)
  have lifted: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss ({}::bool rel) False (\<lambda>_. False)"
    by (rule lpp_stopped_contract_lift_interface[OF commute contract]) simp
  show "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))) {ss}"
    using lifted by (simp add: lp_answer_contract_def)
next
  assume sn: "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))) {ss}"
  have contract: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss ({}::bool rel) False (\<lambda>_. False)"
    using sn by (auto simp: lp_answer_contract_def lp_answers_covered_def)
  have projected: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) (lpc_reinterface F ss) ({}::bool rel) False (\<lambda>_. False)"
    by (rule lpp_stopped_contract_project[OF commute contract]) simp
  show "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))) {lpc_reinterface F ss}"
    using projected by (simp add: lp_answer_contract_def)
qed

ML \<open>
val checked = [@{thm lpp_stopped_reinterface_SN}, @{thm lpp_stopped_reinterface_path_reflect}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped return interface dependency" else ();
\<close>
end
