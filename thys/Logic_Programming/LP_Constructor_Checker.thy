theory LP_Constructor_Checker
  imports LP_Constructor_QDP LP_PiDP_Checker
begin

definition lp_constructor_lhs_check where
  "lp_constructor_lhs_check D l = (case l of Var _ \<Rightarrow> False
    | Fun f ts \<Rightarrow> list_all (\<lambda>t. funs_term t\<inter>D={}) ts)"

lemma lp_constructor_lhs_check_sound:
  "lp_constructor_lhs_check D l \<Longrightarrow> lp_constructor_lhs (-D) l"
  by (cases l) (auto simp: lp_constructor_lhs_check_def lp_constructor_lhs_def list_all_iff)

definition check_lp_constructor where
  "check_lp_constructor I J P outs fallback names marks filters q n positions seed nfs prf =
    (case afs_of filters of None \<Rightarrow> False | Some \<pi> \<Rightarrow>
      let out = (\<lambda>f. the_default f (map_of outs f));
          sharp = (\<lambda>f. the_default f (map_of marks f));
          u = lp_u_lookup fallback names;
          R = lp_translation.translated P id out u;
          ps = lp_translation.pi_pairs P id out u sharp;
          D = lp_pi_defined R;
          data = (\<lambda>f. if f\<in>D then seed else f);
          U = fallback # concat names;
          filtered = map (af_rule \<pi>) R;
          Q = map fst filtered
      in seed\<notin>D \<and> lp_data_fixed_program data P \<and>
         list_all (\<lambda>(l,r). lp_constructor_lhs_check D l) R \<and>
         list_all (\<lambda>(l,r). funs_term l\<inter>D={}) ps \<and>
         list_all (\<lambda>t. case t of Var _\<Rightarrow>False | Fun f ts\<Rightarrow>f\<in>D) Q \<and>
         lp_check_active (U @ map sharp U) \<pi> (map fst filters) \<and>
         lp_check_query \<pi> (sharp q) n positions \<and>
         list_all (\<lambda>(l,r). vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)) (R@ps) \<and>
         isOK (check_dp_termination_proof I J False id
           (dpp_ops.mk J nfs False (map (af_rule \<pi>) ps) [] Q [] filtered) prf))"

lemma lp_map_finite_eval:
  "map_lp_iterm data id (lp_ieval t LPIVar) = lp_ieval (map_term data id t) LPIVar"
  by (induct t) (auto simp: map_map o_def intro!: map_cong)

theorem check_lp_constructor_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_constructor I J P outs fallback names marks filters q n positions seed nfs prf"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
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
  let ?ts = "map (map_term ?data id) ts"
  have ground: "ground (af_term \<pi> (Fun (?sharp q) ?ts))"
    by (rule lp_check_query_sound[OF query]) (use len gr in auto)
  have measured: "lp_iproject \<pi> (mencode ?sharp (lp_data_config ?data
      (LPICall (q,map (\<lambda>t. lp_ieval t LPIVar) ts))))
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
