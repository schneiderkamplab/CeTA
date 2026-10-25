theory LP_Dependency_Triple_Checker
  imports LP_Dependency_Triple_PiDP
begin

definition check_lp_triple_pidp where
  "check_lp_triple_pidp I J D P outs fallback dnames pnames marks filters q n positions labs proofs =
    (case afs_of filters of None \<Rightarrow> False | Some \<pi> \<Rightarrow>
      let out=(\<lambda>f. the_default f (map_of outs f));
          sharp=(\<lambda>f. the_default f (map_of marks f));
          du=lp_u_lookup fallback dnames;
          pu=lp_u_lookup fallback pnames;
          R=lp_triple_translation.dt_support P id out pu;
          ps=lp_triple_translation.dt_pairs D id out sharp du
      in lp_check_query \<pi> (sharp q) n positions \<and>
        list_all (\<lambda>(l,r). is_Fun l) R \<and>
        list_all (\<lambda>(l,r). vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)) (R@ps) \<and>
        lp_pi_graph_check I J (lp_pi_defined R) R ps \<pi> labs proofs)"

theorem check_lp_triple_pidp_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_triple_pidp I J D P outs fallback dnames pnames marks filters q n positions labs proofs"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_triple_calls (set D) P) {(q,map (\<lambda>t. lp_ieval t LPIVar) ts)}"
proof -
  obtain \<pi> where pi: "afs_of filters=Some \<pi>"
    using ok unfolding check_lp_triple_pidp_def by (cases "afs_of filters") auto
  let ?out = "\<lambda>f. the_default f (map_of outs f)"
  let ?sharp = "\<lambda>f. the_default f (map_of marks f)"
  let ?du = "lp_u_lookup fallback dnames"
  let ?pu = "lp_u_lookup fallback pnames"
  interpret lp_triple_translation D P id ?out ?sharp ?du ?pu .
  have query: "lp_check_query \<pi> (?sharp q) n positions"
    and roots: "list_all (\<lambda>(l,r). is_Fun l) dt_support"
    and vars: "list_all (\<lambda>(l,r). vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)) (dt_support@dt_pairs)"
    and graph: "lp_pi_graph_check I J (lp_pi_defined dt_support) dt_support dt_pairs \<pi> labs proofs"
    using ok by (auto simp: check_lp_triple_pidp_def pi Let_def)
  have rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    using vars by (auto simp: list_all_iff)
  have no_chain: "\<And>ls rs valuations.
      \<not> lp_pi_narrow_chain (set dt_pairs) (set dt_support) \<pi> ls rs valuations"
    by (rule lp_pi_graph_check_sound[OF I J graph _ rv], rule lp_pi_defined_roots[OF roots])
  have ground: "ground (af_term \<pi> (Fun (?sharp q) ts))"
    by (rule lp_check_query_sound[OF query len gr])
  have projection: "lp_iproject \<pi> (lp_itag (?sharp \<circ> id) (q,map (\<lambda>t. lp_ieval t LPIVar) ts))
      (af_term \<pi> (Fun (?sharp q) ts))"
  proof -
    have empty: "vars_term (af_term \<pi> (Fun (?sharp q) ts))={}"
      using ground by (simp add: ground_vars_term_empty)
    have "lp_iproject \<pi> (lp_ieval (Fun (?sharp q) ts) LPIVar)
      (af_term \<pi> (Fun (?sharp q) ts) \<cdot> Var)"
      by (rule lp_iproject_ieval_forward) (use empty in blast)
    then show ?thesis by (simp add: lp_itag_def)
  qed
  show ?thesis by (rule dt_pi_chains_imply_triple_termination[OF no_chain projection rv dv])
qed

definition check_lp_initial_triples where
  "check_lp_initial_triples I J D P outs fallback dnames pnames marks filters q n positions labs proofs =
    (D=lp_dependency_triples P \<and>
      check_lp_triple_pidp I J D P outs fallback dnames pnames marks filters q n positions labs proofs)"

theorem check_lp_initial_triples_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_initial_triples I J D P outs fallback dnames pnames marks filters q n positions labs proofs"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof (rule lp_triple_calls_imply_source_termination)
  have D: "D=lp_dependency_triples P" and child:
    "check_lp_triple_pidp I J D P outs fallback dnames pnames marks filters q n positions labs proofs"
    using ok by (auto simp: check_lp_initial_triples_def)
  show "SN_on (lp_triple_calls (set (lp_dependency_triples P)) P)
    {(q,map (\<lambda>t. lp_ieval t LPIVar) ts)}"
    using check_lp_triple_pidp_sound[OF I J child len gr] by (simp add: D)
qed

end
