theory LP_Dependency_Triple_Projected_Query
 imports LP_Dependency_Triple_Observed_Roles
begin

text \<open>The existing PiDP proof needs a finite selected projection of its
entry. Whole-value groundness is one sufficient premise; checked return shapes
can provide the same premise while permitting unobserved rational subterms.\<close>

theorem check_lp_triple_pidp_projected_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) lp_iterm list"
    and projected :: "(('f,nat list) lab,string) term"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_triple_pidp I J D P outs fallback dnames pnames marks filters q n positions labs proofs"
    and filter: "afs_of filters=Some flt"
    and projection: "lp_iproject flt
      (LPIFun (the_default q (map_of marks q)) ts) projected"
  shows "SN_on (lp_triple_calls (set D) P) {(q,ts)}"
proof -
  let ?out = "\<lambda>f. the_default f (map_of outs f)"
  let ?sharp = "\<lambda>f. the_default f (map_of marks f)"
  let ?du = "lp_u_lookup fallback dnames"
  let ?pu = "lp_u_lookup fallback pnames"
  interpret lp_triple_translation D P id ?out ?sharp ?du ?pu .
  have query: "lp_check_query flt (?sharp q) n positions"
    and roots: "list_all (\<lambda>(l,r). is_Fun l) dt_support"
    and vars: "list_all (\<lambda>(l,r). vars_term (af_term flt r)\<subseteq>vars_term (af_term flt l)) (dt_support@dt_pairs)"
    and graph: "lp_pi_graph_check I J (lp_pi_defined dt_support) dt_support dt_pairs flt labs proofs"
    using ok by (auto simp: check_lp_triple_pidp_def filter Let_def)
  have rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow>
      vars_term (af_term flt r)\<subseteq>vars_term (af_term flt l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow>
      vars_term (af_term flt r)\<subseteq>vars_term (af_term flt l)"
    using vars by (auto simp: list_all_iff)
  have no_chain: "\<And>ls rs valuations.
      \<not> lp_pi_narrow_chain (set dt_pairs) (set dt_support) flt ls rs valuations"
    by (rule lp_pi_graph_check_sound[OF I J graph _ rv], rule lp_pi_defined_roots[OF roots])
  have projected_call: "lp_iproject flt (lp_itag (?sharp \<circ> id) (q,ts)) projected"
    using projection by (simp add: lp_itag_def o_def lp_observed_map_identity map_idI)
  show ?thesis by (rule dt_pi_chains_imply_triple_termination[OF no_chain projected_call rv dv])
qed

theorem check_lp_triple_pidp_projected_roles_sound:
  fixes fallback :: "(string,nat list) lab" and ts :: "('f,string) lp_iterm list"
    and projected :: "((string,nat list) lab,string) term"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and child: "check_lp_triple_pidp I J (lp_roles_triples p d D) (lp_roles_program p d P)
      outs fallback dnames pnames marks filters (p q) n positions labs proofs"
    and filter: "afs_of filters=Some flt"
    and projection: "lp_iproject flt (LPIFun (the_default (p q) (map_of marks (p q)))
      (map (map_lp_iterm d id) ts)) projected"
  shows "SN_on (lp_triple_calls (set D) P) {(q,ts)}"
proof -
  have child_sn: "SN_on (lp_triple_calls (set (lp_roles_triples p d D)) (lp_roles_program p d P))
      {(p q,map (map_lp_iterm d id) ts)}"
    by (rule check_lp_triple_pidp_projected_sound[OF I J child filter projection])
  show ?thesis
    by (rule lp_roles_triple_termination_reflect[where p=p and d=d])
      (use child_sn in \<open>simp add: lp_roles_iatom_def\<close>)
qed

ML \<open>
val checked = [@{thm check_lp_triple_pidp_projected_sound}, @{thm check_lp_triple_pidp_projected_roles_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted projected triple query" else ();
\<close>
end
