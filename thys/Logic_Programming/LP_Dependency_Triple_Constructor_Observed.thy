theory LP_Dependency_Triple_Constructor_Observed
 imports LP_Dependency_Triple_Constructor_Checker LP_Dependency_Triple_Observed_Roles
begin

theorem check_lp_triple_constructor_observed_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) lp_iterm list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_triple_constructor I J D P outs fallback dnames pnames marks filters q n positions seed nfs prf"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> lp_seg_ground (ts!i)"
  shows "SN_on (lp_triple_calls (set D) P) {(q,ts)}"
proof -
  interpret dpp_spec J by (rule J)
  obtain \<pi> where pi: "afs_of filters=Some \<pi>"
    using ok unfolding check_lp_triple_constructor_def by (cases "afs_of filters") auto
  let ?out="\<lambda>f. the_default f (map_of outs f)"
  let ?sharp="\<lambda>f. the_default f (map_of marks f)"
  let ?du="lp_u_lookup fallback dnames"
  let ?pu="lp_u_lookup fallback pnames"
  interpret lp_triple_translation D P id ?out ?sharp ?du ?pu .
  let ?Def="lp_pi_defined dt_support"
  let ?C="-?Def"
  let ?data="\<lambda>f. if f\<in>?Def then seed else f"
  let ?U="(fallback # concat pnames) @ map ?sharp (fallback # concat dnames)"
  let ?V="set ?U"
  let ?Q="map fst (map (af_rule \<pi>) dt_support)"
  have seed: "seed\<notin>?Def" and fixed: "lp_data_fixed_program ?data P"
    and fixed_triples: "list_all (\<lambda>(h,ps,b). lp_data_fixed_atom ?data h \<and>
      list_all (lp_data_fixed_atom ?data) ps \<and> lp_data_fixed_atom ?data b) D"
    and shapes: "list_all (\<lambda>(l,r). lp_constructor_lhs_check ?Def l) dt_support"
    and pairs: "list_all (\<lambda>(l,r). funs_term l\<inter>?Def={}) dt_pairs"
    and qroots: "list_all (\<lambda>t. case t of Var _\<Rightarrow>False | Fun f ts\<Rightarrow>f\<in>?Def) ?Q"
    and active: "lp_check_active ?U \<pi> (map fst filters)"
    and query: "lp_check_query \<pi> (?sharp q) n positions"
    and vars: "list_all (\<lambda>(l,r). vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)) (dt_support@dt_pairs)"
    and child: "isOK (check_dp_termination_proof I J False id
      (dpp_ops.mk J nfs False (map (af_rule \<pi>) dt_pairs) [] ?Q [] (map (af_rule \<pi>) dt_support)) prf)"
    using ok by (auto simp: check_lp_triple_constructor_def pi Let_def)
  have range: "range ?data\<subseteq>?C" using seed by auto
  have shape: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow> lp_constructor_lhs ?C l"
    using shapes by (auto simp: list_all_iff dest: lp_constructor_lhs_check_sound)
  have support_shape: "\<And>l r. (l,r)\<in>set (lp_translation.translated P id ?out ?pu) \<Longrightarrow>
      lp_constructor_lhs ?C l"
  proof -
    fix l r assume member: "(l,r)\<in>set (lp_translation.translated P id ?out ?pu)"
    have support_member: "(l,r)\<in>set dt_support"
      using member by (simp only: dt_support_def)
    show "lp_constructor_lhs ?C l" by (rule shape[OF support_member])
  qed
  have triple: "\<And>h ps b. (h,ps,b)\<in>set D \<Longrightarrow>
      lp_data_fixed_atom ?data h \<and> list_all (lp_data_fixed_atom ?data) ps \<and> lp_data_fixed_atom ?data b"
    using fixed_triples by (auto simp: list_all_iff)
  have pair: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow> funs_term l\<subseteq>?C"
    using pairs by (auto simp: list_all_iff)
  have roots: "\<And>t. t\<in>set ?Q \<Longrightarrow> \<exists>f us. t=Fun f us \<and> f\<notin>?C"
  proof -
    fix t assume t: "t\<in>set ?Q"
    have "case t of Var _\<Rightarrow>False | Fun f ts\<Rightarrow>f\<in>?Def"
      using qroots t unfolding list_all_iff by blast
    then show "\<exists>f us. t=Fun f us \<and> f\<notin>?C" by (cases t) auto
  qed
  have frame: "\<And>c i. ?pu c i\<in>?V"
    using lp_triple_u_member[of fallback pnames] by auto
  have marked: "\<And>c i. ?sharp (?du c i)\<in>?V"
  proof -
    fix c i
    have raw: "?du c i\<in>set (fallback # concat dnames)"
      by (rule lp_triple_u_member)
    have "?sharp (?du c i)\<in>?sharp ` set (fallback # concat dnames)"
      by (rule imageI[OF raw])
    then show "?sharp (?du c i)\<in>?V" by auto
  qed
  have filter: "lp_filter \<pi> ?V"
    by (rule lp_check_active_sound[OF _ active])
      (simp_all add: afs_of_Some_afs_syms[OF pi])
  have rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    using vars by (auto simp: list_all_iff)
  have finite: "finite_dpp (nfs,False,af_rule \<pi> ` set dt_pairs,{},set ?Q,{},af_rule \<pi> ` set dt_support)"
    using check_dp_termination_proof[OF I J child] by (simp add: mk_sound)
  obtain measure :: "(('f,nat list) lab,string) term" where measured:
    "lp_iproject \<pi> (lp_itag (?sharp \<circ> id) (lp_data_atom ?data (q,ts))) measure"
    using lp_check_query_infinite_projection[OF query len gr, where data="?data"]
    by (auto simp: lp_data_atom_def lp_itag_def)
  show ?thesis
    apply (rule dt_constructor_qdp_termination[where C="?C" and U="?V" and Q="set ?Q" and data="?data"])
    apply (rule fixed)
    apply (rule range)
    apply (rule support_shape, assumption)
    apply (rule frame)
    apply (rule marked)
    apply (rule triple, assumption)
    apply (rule filter)
    apply (rule measured)
    apply (rule rv, assumption)
    apply (rule dv, assumption)
    apply (rule pair, assumption)
    apply (rule roots, assumption)
    apply (rule finite)
    done
qed

theorem check_lp_triple_constructor_observed_roles_sound:
  fixes fallback :: "(string,nat list) lab"
    and ts :: "('f,string) lp_iterm list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and child: "check_lp_triple_constructor I J (lp_roles_triples p d D) (lp_roles_program p d P)
      outs fallback dnames pnames marks filters (p q) n positions seed nfs prf"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> lp_seg_ground (ts!i)"
  shows "SN_on (lp_triple_calls (set D) P) {(q,ts)}"
proof -
  have mapped_ground: "lp_seg_ground ((map (map_lp_iterm d id) ts)!i)"
    if "i\<in>set positions" "i<n" for i
    using lp_seg_ground_map_symbols[OF gr[OF that], of d] that len by simp
  have child_sn: "SN_on (lp_triple_calls (set (lp_roles_triples p d D)) (lp_roles_program p d P))
      {(p q,map (map_lp_iterm d id) ts)}"
    by (rule check_lp_triple_constructor_observed_sound[OF I J child _ mapped_ground]) (simp add: len)
  show ?thesis
    by (rule lp_roles_triple_termination_reflect[where p=p and d=d])
      (use child_sn in \<open>simp add: lp_roles_iatom_def\<close>)
qed

ML \<open>
val checked = [@{thm check_lp_triple_constructor_observed_sound}, @{thm check_lp_triple_constructor_observed_roles_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted observed constructor triple query" else ();
\<close>
end
