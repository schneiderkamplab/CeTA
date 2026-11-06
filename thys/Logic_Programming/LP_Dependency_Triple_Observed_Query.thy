theory LP_Dependency_Triple_Observed_Query
 imports LP_Dependency_Triple_Checker LP_Constructor_Infinite_Query
begin

lemma lp_observed_map_identity: "map_lp_iterm id id (t :: ('a,'b) lp_iterm)=t"
  by (rule lp_iterm.map_id)

theorem check_lp_triple_pidp_observed_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) lp_iterm list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_triple_pidp I J D P outs fallback dnames pnames marks filters q n positions labs proofs"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> lp_seg_ground (ts!i)"
  shows "SN_on (lp_triple_calls (set D) P) {(q,ts)}"
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
  have unchanged: "map (map_lp_iterm id id) ts=ts"
    by (rule map_idI) (rule lp_observed_map_identity)
  obtain projected :: "(('f,nat list) lab,string) term" where projection:
    "lp_iproject \<pi> (lp_itag (?sharp \<circ> id) (q,ts)) projected"
    using lp_check_query_infinite_projection[where data=id, OF query len gr]
    by (auto simp: lp_itag_def unchanged o_def)
  show ?thesis by (rule dt_pi_chains_imply_triple_termination[OF no_chain projection rv dv])
qed

ML \<open>
val checked = [@{thm check_lp_triple_pidp_observed_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted observed triple query" else ();
\<close>
end
