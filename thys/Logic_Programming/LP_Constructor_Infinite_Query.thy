theory LP_Constructor_Infinite_Query
 imports LP_Constructor_Checker LP_Symbolic_Evaluation
begin

lemma lp_seg_ground_mapped_projection:
  fixes pi :: "'f afs" and u :: "('f,'v) lp_iterm" and data :: "'f \<Rightarrow> 'f"
  assumes ground: "lp_seg_ground u"
  shows "\<exists>t::('f,'v) term. lp_iproject pi (map_lp_iterm data id u) t"
proof -
  obtain s :: "('f,'v) term" where finite: "ground s" "lp_ieval s LPIVar=u"
    using lp_seg_ground_finite[OF ground] by blast
  have empty: "vars_term (af_term pi (map_term data id s))={}"
    using lp_ground_filter[of "map_term data id s" pi] finite(1)
    by (simp add: ground_vars_term_empty[symmetric])
  have projection: "lp_iproject pi (lp_ieval (map_term data id s) LPIVar)
      (af_term pi (map_term data id s)\<cdot>Var)"
    by (rule lp_iproject_ieval_forward) (use empty in blast)
  show ?thesis using projection finite(2)
    by (auto simp: lp_map_finite_eval)
qed

lemma lp_check_query_infinite_projection:
  fixes pi :: "'f afs" and ts :: "('f,'v) lp_iterm list" and data :: "'f \<Rightarrow> 'f"
  assumes query: "lp_check_query pi q n positions" and len: "length ts=n"
    and ground: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> lp_seg_ground (ts!i)"
  shows "\<exists>t::('f,'v) term. lp_iproject pi (LPIFun q (map (map_lp_iterm data id) ts)) t"
proof -
  obtain ps where filter: "afs pi (q,n) = AFList ps" and selected: "set ps \<subseteq> set positions"
    using query unfolding lp_check_query_def by (cases "afs pi (q,n)") (auto simp: list_all_iff)
  have bounds: "set ps\<subseteq>{0..<n}"
    using Argument_Filter.afs[of n pi q] by (auto simp: filter)
  have each: "\<exists>t::('f,'v) term. i<length ts \<and> lp_iproject pi (map_lp_iterm data id (ts!i)) t"
    if "i\<in>set ps" for i
  proof -
    have bound: "i<n" and member: "i\<in>set positions" using bounds selected that by auto
    have gr: "lp_seg_ground (ts!i)" by (rule ground[OF member bound])
    have "\<exists>t::('f,'v) term. lp_iproject pi (map_lp_iterm data id (ts!i)) t"
      by (rule lp_seg_ground_mapped_projection[OF gr])
    then show ?thesis using bound len by auto
  qed
  let ?pick = "\<lambda>i. SOME t::('f,'v) term. lp_iproject pi (map_lp_iterm data id (ts!i)) t"
  have witness: "lp_iproject pi (map_lp_iterm data id (ts!i)) (?pick i)"
    if "i\<in>set ps" for i
    by (rule someI_ex) (use each[OF that] in blast)
  have projected: "lp_iproject pi (LPIFun q (map (map_lp_iterm data id) ts)) (Fun q (map ?pick ps))"
  proof (rule lp_iproject.list)
    show "afs pi (q,length (map (map_lp_iterm data id) ts))=AFList ps"
      using filter len by simp
    show "list_all2 (\<lambda>i t. i<length (map (map_lp_iterm data id) ts) \<and>
        lp_iproject pi (map (map_lp_iterm data id) ts!i) t) ps (map ?pick ps)"
      unfolding list_all2_map2 list_all2_same list_all_iff
    proof (intro ballI)
      fix i assume member: "i\<in>set ps"
      have bound: "i<length ts" using bounds member len by auto
      show "i<length (map (map_lp_iterm data id) ts) \<and>
          lp_iproject pi (map (map_lp_iterm data id) ts!i) (?pick i)"
        using bound witness[OF member] by simp
    qed
  qed
  show ?thesis using projected by blast
qed

theorem check_lp_constructor_infinite_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) lp_iterm list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_constructor I J P outs fallback names marks filters q n positions seed nfs prf"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> lp_seg_ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,ts)]}"
proof -
  interpret dpp_spec J by (rule J)
  obtain \<pi> where pi: "afs_of filters=Some \<pi>"
    using ok unfolding check_lp_constructor_def by (cases "afs_of filters") auto
  let ?out = "\<lambda>f. the_default f (map_of outs f)"
  let ?sharp = "\<lambda>f. the_default f (map_of marks f)"
  let ?u = "lp_u_lookup fallback names"
  interpret lp_translation P id ?out ?u .
  let ?D = "lp_pi_defined translated"
  let ?C = "-?D"
  let ?data = "\<lambda>f. if f\<in>?D then seed else f"
  let ?U = "fallback # concat names"
  let ?V = "set (?U @ map ?sharp ?U)"
  let ?Q = "map fst (map (af_rule \<pi>) translated)"
  have seed: "seed\<notin>?D" and fixed: "lp_data_fixed_program ?data P"
    and shapes: "list_all (\<lambda>(l,r). lp_constructor_lhs_check ?D l) translated"
    and pairs: "list_all (\<lambda>(l,r). funs_term l\<inter>?D={}) (pi_pairs ?sharp)"
    and qroots: "list_all (\<lambda>t. case t of Var _\<Rightarrow>False | Fun f ts\<Rightarrow>f\<in>?D) ?Q"
    and active: "lp_check_active (?U @ map ?sharp ?U) \<pi> (map fst filters)"
    and query: "lp_check_query \<pi> (?sharp q) n positions"
    and vars: "list_all (\<lambda>(l,r). vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)) (translated@pi_pairs ?sharp)"
    and child: "isOK (check_dp_termination_proof I J False id
      (dpp_ops.mk J nfs False (map (af_rule \<pi>) (pi_pairs ?sharp)) [] ?Q [] (map (af_rule \<pi>) translated)) prf)"
    using ok by (auto simp: check_lp_constructor_def pi Let_def)
  have range: "range ?data\<subseteq>?C" using seed by auto
  have shape: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs ?C l"
    using shapes by (auto simp: list_all_iff dest: lp_constructor_lhs_check_sound)
  have pair: "\<And>l r. (l,r)\<in>set (pi_pairs ?sharp) \<Longrightarrow> funs_term l\<subseteq>?C"
    using pairs by (auto simp: list_all_iff)
  have roots: "\<And>t. t\<in>set ?Q \<Longrightarrow> \<exists>f us. t=Fun f us \<and> f\<notin>?C"
  proof -
    fix t assume t: "t\<in>set ?Q"
    have "case t of Var _\<Rightarrow>False | Fun f ts\<Rightarrow>f\<in>?D"
      using qroots t unfolding list_all_iff by blast
    then show "\<exists>f us. t=Fun f us \<and> f\<notin>?C" by (cases t) auto
  qed
  have umem: "\<And>c i. ?u c i\<in>set ?U"
  proof -
    fix c i
    have "?u c i\<in>range (\<lambda>(c,i). ?u c i)"
      by (rule image_eqI[where x="(c,i)"]) simp_all
    then show "?u c i\<in>set ?U" using lp_u_range[of fallback names] by blast
  qed
  have frame: "\<And>c i. ?u c i\<in>?V"
    by (simp only: set_append) (blast intro: umem)
  have marked: "\<And>c i. ?sharp (?u c i)\<in>?V"
  proof -
    fix c i
    have "?sharp (?u c i)\<in>?sharp ` set ?U" by (rule imageI[OF umem])
    then show "?sharp (?u c i)\<in>?V" by (simp only: set_append list.set_map) blast
  qed
  have filter: "lp_filter \<pi> ?V"
    by (rule lp_check_active_sound[OF _ active])
      (simp_all add: afs_of_Some_afs_syms[OF pi])
  have rv: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set (pi_pairs ?sharp) \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    using vars by (auto simp: list_all_iff)
  have finite: "finite_dpp (nfs,False,af_rule \<pi> ` set (pi_pairs ?sharp),{},set ?Q,{},af_rule \<pi> ` set translated)"
    using check_dp_termination_proof[OF I J child] by (simp add: mk_sound)
  obtain measure :: "(('f,nat list) lab,string) term" where measured: "lp_iproject \<pi> (mencode ?sharp (lp_data_config ?data
      (LPICall (q,ts)))) measure"
    using lp_check_query_infinite_projection[OF query len gr, where data="?data"]
    by (auto simp: lp_data_atom_def lp_itag_def)
  show ?thesis
    apply (rule constructor_qdp_source_termination[where C="?C" and U="?V" and Q="set ?Q" and data="?data"])
    apply (rule fixed)
    apply (rule range)
    apply (rule shape, assumption)
    apply (rule frame)
    apply (rule marked)
    apply (rule filter)
    apply (rule measured)
    apply (rule rv, assumption)
    apply (rule dv, assumption)
    apply (rule pair, assumption)
    apply (rule roots, assumption)
    apply (rule finite)
    done
qed

end
