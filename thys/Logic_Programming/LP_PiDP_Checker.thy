theory LP_PiDP_Checker
  imports LP_PiDP_Source LP_PiDP_Graph LP_Mode_Checker
begin

definition lp_pi_rank where
  "lp_pi_rank ps labs p = the_default 0 (map_of (zip ps labs) p)"

definition lp_pi_component where
  "lp_pi_component I J D R ps \<pi> option_prf = (case option_prf of
    None \<Rightarrow> list_all (\<lambda>p. list_all (\<lambda>q.
      \<not> lp_shapes_compatible (lp_shape_cap D (snd p)) (fst q)) ps) ps
  | Some child_cert \<Rightarrow> isOK (check_dp_termination_proof I J False id
      (dpp_ops.mk J False False (map (af_rule \<pi>) ps) [] [] [] (map (af_rule \<pi>) R)) child_cert))"

definition lp_pi_graph_check where
  "lp_pi_graph_check I J D R ps \<pi> labs proofs =
    (let rank = lp_pi_rank ps labs in
    length labs=length ps \<and>
    list_all (\<lambda>p. rank p<length proofs) ps \<and>
    list_all (\<lambda>p. list_all (\<lambda>q.
      lp_shapes_compatible (lp_shape_cap D (snd p)) (fst q) \<longrightarrow> rank q\<le>rank p) ps) ps \<and>
    list_all (\<lambda>i. lp_pi_component I J D R (filter (\<lambda>p. rank p=i) ps) \<pi> (proofs!i)) [0..<length proofs])"

lemma lp_pi_component_sound:
  fixes R ps :: "(('f::{compare_order,countable,showl},nat list) lab,string) rule list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "lp_pi_component I J D R ps \<pi> option_prf"
    and roots: "\<And>l r. (l,r)\<in>set R \<Longrightarrow> \<exists>f ts. l=Fun f ts \<and> f\<in>D"
    and vars: "\<And>l r. (l,r)\<in>set R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  shows "\<not> lp_pi_narrow_chain (set ps) (set R) \<pi> ls rs valuations"
proof (cases option_prf)
  case None
  show ?thesis
  proof
    assume chain: "lp_pi_narrow_chain (set ps) (set R) \<pi> ls rs valuations"
    have p: "(ls 0,rs 0)\<in>set ps" and q: "(ls 1,rs 1)\<in>set ps"
      and link: "(lp_ieval (rs 0) (valuations 0),lp_ieval (ls 1) (valuations 1))\<in>(lp_pi_link (set R))\<^sup>*"
      using chain unfolding lp_pi_narrow_chain_def by (auto dest: spec[where x=0] spec[where x=1])
    have edge: "lp_shapes_compatible (lp_shape_cap D (rs 0)) (ls 1)"
      by (rule lp_pi_graph_edge[OF link roots])
    have absent: "\<forall>p\<in>set ps. \<forall>q\<in>set ps. \<not> lp_shapes_compatible (lp_shape_cap D (snd p)) (fst q)"
      using ok by (simp add: lp_pi_component_def None list_all_iff)
    show False using bspec[OF bspec[OF absent p] q] edge by simp
  qed
next
  case (Some child_cert)
  interpret dpp_spec J by (rule J)
  have checked: "isOK (check_dp_termination_proof I J False id
      (dpp_ops.mk J False False (map (af_rule \<pi>) ps) [] [] [] (map (af_rule \<pi>) R)) child_cert)"
    using ok by (simp add: lp_pi_component_def Some)
  have finite: "finite_dpp (False,False,af_rule \<pi> ` set ps,{},{},{},af_rule \<pi> ` set R)"
    using check_dp_termination_proof[OF I J checked] by (simp add: mk_sound)
  show ?thesis by (rule lp_pi_narrow_filter_processor[OF finite vars])
qed

lemma lp_pi_graph_check_sound:
  fixes R ps :: "(('f::{compare_order,countable,showl},nat list) lab,string) rule list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "lp_pi_graph_check I J D R ps \<pi> labs proofs"
    and roots: "\<And>l r. (l,r)\<in>set R \<Longrightarrow> \<exists>f ts. l=Fun f ts \<and> f\<in>D"
    and vars: "\<And>l r. (l,r)\<in>set R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  shows "\<not> lp_pi_narrow_chain (set ps) (set R) \<pi> ls rs valuations"
proof (rule lp_pi_graph_decomposition[where rank="lp_pi_rank ps labs", OF roots])
  fix l r l' r'
  assume "(l,r)\<in>set ps" "(l',r')\<in>set ps"
    "lp_shapes_compatible (lp_shape_cap D r) l'"
  then show "lp_pi_rank ps labs (l',r')\<le>lp_pi_rank ps labs (l,r)"
    using ok by (auto simp: lp_pi_graph_check_def Let_def list_all_iff)
next
  fix k ls rs valuations
  show "\<not> lp_pi_narrow_chain {p\<in>set ps. lp_pi_rank ps labs p=k} (set R) \<pi> ls rs valuations"
  proof (cases "k<length proofs")
    case True
    have checked: "lp_pi_component I J D R (filter (\<lambda>p. lp_pi_rank ps labs p=k) ps) \<pi> (proofs!k)"
      using ok True by (auto simp: lp_pi_graph_check_def Let_def list_all_iff)
    show ?thesis using lp_pi_component_sound[OF I J checked roots vars] by simp
  next
    case False
    have empty: "{p\<in>set ps. lp_pi_rank ps labs p=k}={}"
      using ok False by (auto simp: lp_pi_graph_check_def Let_def list_all_iff)
    show ?thesis by (simp add: empty lp_pi_narrow_chain_def)
  qed
qed

definition lp_pi_defined where
  "lp_pi_defined R = set (concat (map (\<lambda>(l,r). case l of Var x\<Rightarrow>[] | Fun f ts\<Rightarrow>[f]) R))"

lemma lp_pi_defined_roots:
  "list_all (\<lambda>(l,r). is_Fun l) R \<Longrightarrow> (l,r)\<in>set R \<Longrightarrow>
    \<exists>f ts. l=Fun f ts \<and> f\<in>lp_pi_defined R"
  unfolding lp_pi_defined_def list_all_iff by (cases l) force+

definition check_lp_pidp where
  "check_lp_pidp I J P outs fallback names marks filters q n positions labs proofs =
    (case afs_of filters of None \<Rightarrow> False | Some \<pi> \<Rightarrow>
      let out = (\<lambda>f. the_default f (map_of outs f));
          sharp = (\<lambda>f. the_default f (map_of marks f));
          u = lp_u_lookup fallback names;
          R = lp_translation.translated P id out u;
          ps = lp_translation.pi_pairs P id out u sharp
      in lp_check_query \<pi> (sharp q) n positions \<and>
         list_all (\<lambda>(l,r). is_Fun l) R \<and>
         list_all (\<lambda>(l,r). vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)) (R@ps) \<and>
         lp_pi_graph_check I J (lp_pi_defined R) R ps \<pi> labs proofs)"

theorem check_lp_pidp_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_pidp I J P outs fallback names marks filters q n positions labs proofs"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  obtain \<pi> where pi: "afs_of filters=Some \<pi>"
    using ok unfolding check_lp_pidp_def by (cases "afs_of filters") auto
  let ?out = "\<lambda>f. the_default f (map_of outs f)"
  let ?sharp = "\<lambda>f. the_default f (map_of marks f)"
  let ?u = "lp_u_lookup fallback names"
  interpret lp_translation P id ?out ?u .
  have query: "lp_check_query \<pi> (?sharp q) n positions"
    and roots: "list_all (\<lambda>(l,r). is_Fun l) translated"
    and vars: "list_all (\<lambda>(l,r). vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)) (translated@pi_pairs ?sharp)"
    and graph: "lp_pi_graph_check I J (lp_pi_defined translated) translated (pi_pairs ?sharp) \<pi> labs proofs"
    using ok by (auto simp: check_lp_pidp_def pi Let_def)
  have rv: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set (pi_pairs ?sharp) \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
    using vars by (auto simp: list_all_iff)
  have no_chain: "\<And>ls rs valuations. \<not> lp_pi_narrow_chain (set (pi_pairs ?sharp)) (set translated) \<pi> ls rs valuations"
    by (rule lp_pi_graph_check_sound[OF I J graph _ rv], rule lp_pi_defined_roots[OF roots])
  have ground: "ground (af_term \<pi> (Fun (?sharp q) ts))"
    by (rule lp_check_query_sound[OF query len gr])
  have pr: "lp_iproject \<pi> (lp_ieval (Fun (?sharp q) ts) LPIVar) (af_term \<pi> (Fun (?sharp q) ts))"
  proof -
    have empty: "vars_term (af_term \<pi> (Fun (?sharp q) ts))={}"
      using ground by (simp add: ground_vars_term_empty)
    have projection: "lp_iproject \<pi> (lp_ieval (Fun (?sharp q) ts) LPIVar)
      (af_term \<pi> (Fun (?sharp q) ts) \<cdot> Var)"
      by (rule lp_iproject_ieval_forward) (use empty in blast)
    show ?thesis using projection by simp
  qed
  have measured: "lp_iproject \<pi> (mencode ?sharp (LPICall (q,map (\<lambda>t. lp_ieval t LPIVar) ts)))
      (af_term \<pi> (Fun (?sharp q) ts))"
    using pr by (simp add: lp_itag_def)
  show ?thesis by (rule pi_chains_imply_source_termination[OF no_chain measured rv dv])
qed

end
