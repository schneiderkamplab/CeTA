theory LP_Dependency_Triple_Constructor_Checker
  imports LP_Dependency_Triple_Constructor_Chain LP_Constructor_Checker
begin

definition check_lp_triple_constructor where
  "check_lp_triple_constructor I J D P outs fallback dnames pnames marks filters q n positions seed nfs prf =
    (case afs_of filters of None \<Rightarrow> False | Some \<pi> \<Rightarrow>
      let out=(\<lambda>f. the_default f (map_of outs f));
          sharp=(\<lambda>f. the_default f (map_of marks f));
          du=lp_u_lookup fallback dnames; pu=lp_u_lookup fallback pnames;
          R=lp_triple_translation.dt_support P id out pu;
          ps=lp_triple_translation.dt_pairs D id out sharp du;
          Def=lp_pi_defined R;
          data=(\<lambda>f. if f\<in>Def then seed else f);
          U=(fallback # concat pnames) @ map sharp (fallback # concat dnames);
          filtered=map (af_rule \<pi>) R; Q=map fst filtered
      in seed\<notin>Def \<and> lp_data_fixed_program data P \<and>
        list_all (\<lambda>(h,ps,b). lp_data_fixed_atom data h \<and>
          list_all (lp_data_fixed_atom data) ps \<and> lp_data_fixed_atom data b) D \<and>
        list_all (\<lambda>(l,r). lp_constructor_lhs_check Def l) R \<and>
        list_all (\<lambda>(l,r). funs_term l\<inter>Def={}) ps \<and>
        list_all (\<lambda>t. case t of Var _\<Rightarrow>False | Fun f ts\<Rightarrow>f\<in>Def) Q \<and>
        lp_check_active U \<pi> (map fst filters) \<and>
        lp_check_query \<pi> (sharp q) n positions \<and>
        list_all (\<lambda>(l,r). vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)) (R@ps) \<and>
        isOK (check_dp_termination_proof I J False id
          (dpp_ops.mk J nfs False (map (af_rule \<pi>) ps) [] Q [] filtered) prf))"

lemma lp_triple_u_member:
  "lp_u_lookup fallback names c i\<in>set (fallback # concat names)"
proof -
  have "lp_u_lookup fallback names c i\<in>range (\<lambda>(c,i). lp_u_lookup fallback names c i)"
    by (rule image_eqI[where x="(c,i)"]) simp_all
  then show ?thesis using lp_u_range[of fallback names] by blast
qed

theorem check_lp_triple_constructor_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_triple_constructor I J D P outs fallback dnames pnames marks filters q n positions seed nfs prf"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_triple_calls (set D) P) {(q,map (\<lambda>t. lp_ieval t LPIVar) ts)}"
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
  let ?ts="map (map_term ?data id) ts"
  have ground: "ground (af_term \<pi> (Fun (?sharp q) ?ts))"
    by (rule lp_check_query_sound[OF query]) (use len gr in auto)
  have measured: "lp_iproject \<pi> (lp_itag (?sharp \<circ> id)
      (lp_data_atom ?data (q,map (\<lambda>t. lp_ieval t LPIVar) ts)))
      (af_term \<pi> (Fun (?sharp q) ?ts))"
  proof -
    have empty: "vars_term (af_term \<pi> (Fun (?sharp q) ?ts))={}"
      using ground by (simp add: ground_vars_term_empty)
    have pr: "lp_iproject \<pi> (lp_ieval (Fun (?sharp q) ?ts) LPIVar)
      (af_term \<pi> (Fun (?sharp q) ?ts)\<cdot>Var)"
      by (rule lp_iproject_ieval_forward) (use empty in blast)
    show ?thesis using pr
      by (simp add: lp_data_atom_def lp_itag_def map_map o_def lp_map_finite_eval)
  qed
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

end
