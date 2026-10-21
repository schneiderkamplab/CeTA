theory LP_Finite_Checker
  imports LP_Leftmost_Resolution
begin

definition lp_u_lookup where
  "lp_u_lookup fallback names c i =
    (if c < length names \<and> i < length (names!c) then names!c!i else fallback)"

lemma lp_u_range:
  "range (\<lambda>(c,i). lp_u_lookup fallback names c i) \<subseteq> set (fallback # concat names)"
proof
  fix f assume "f \<in> range (\<lambda>(c,i). lp_u_lookup fallback names c i)"
  then obtain c i where f: "f = lp_u_lookup fallback names c i" by auto
  show "f \<in> set (fallback # concat names)"
  proof (cases "c < length names \<and> i < length (names!c)")
    case True
    have row: "names!c \<in> set names" by (rule nth_mem) (use True in simp)
    have item: "names!c!i \<in> set (names!c)" by (rule nth_mem) (use True in simp)
    have member: "names!c!i \<in> set (concat names)"
      unfolding set_concat by (rule UnionI[OF _ item], rule imageI[OF row])
    show ?thesis using member by (simp add: f lp_u_lookup_def True)
  next
    case False
    show ?thesis by (simp add: f lp_u_lookup_def False)
  qed
qed

fun lp_active_entry where
  "lp_active_entry (AFList (0#ps)) = list_all (\<lambda>i. i>0) ps"
| "lp_active_entry _ = False"

lemma lp_active_entry_sound:
  assumes "wf_af_entry (Suc n) e" "lp_active_entry e"
  shows "\<exists>indices. e = AFList (0 # map Suc indices) \<and> set indices \<subseteq> {0..<n}"
proof -
  obtain ps where e: "e = AFList (0#ps)" and pos: "\<forall>i\<in>set ps. i>0"
    using assms(2) by (cases e rule: lp_active_entry.cases) (auto simp: list_all_iff)
  have bound: "\<forall>i\<in>set ps. i<Suc n" using assms(1) by (simp add: e)
  have eq: "map Suc (map (\<lambda>i. i-1) ps) = ps"
    using pos by (induct ps) auto
  have pred_bound: "\<And>i. i \<in> set ps \<Longrightarrow> i-1<n"
  proof -
    fix i assume mem: "i \<in> set ps"
    have "0<i" "i<Suc n" using pos bound mem by blast+
    then show "i-1<n" by arith
  qed
  show ?thesis by (rule exI[where x="map (\<lambda>i. i-1) ps"])
    (use e eq pred_bound in auto)
qed

definition lp_check_active where
  "lp_check_active U \<pi> fs = list_all (\<lambda>(f,n).
    f \<notin> set U \<or> n=0 \<or> lp_active_entry (afs \<pi> (f,n))) fs"

lemma lp_check_active_sound:
  assumes coverage: "afs_syms \<pi> \<subseteq> set fs" and ok: "lp_check_active U \<pi> fs"
    and sub: "V \<subseteq> set U"
  shows "lp_filter \<pi> V"
proof
  fix f n assume f: "f \<in> V"
  show "\<exists>indices. afs \<pi> (f,Suc n) = AFList (0 # map Suc indices) \<and> set indices \<subseteq> {0..<n}"
  proof (cases "(f,Suc n) \<in> afs_syms \<pi>")
    case True
    have member: "(f,Suc n) \<in> set fs" using coverage True by blast
    have ff: "f \<in> set U" using sub f by blast
    have active: "lp_active_entry (afs \<pi> (f,Suc n))"
      using bspec[OF ok[unfolded lp_check_active_def list_all_iff] member] ff by simp
    show ?thesis by (rule lp_active_entry_sound[OF Argument_Filter.afs active])
  next
    case False
    have eq: "afs \<pi> (f,Suc n) = AFList [0..<Suc n]"
      using afs_syms[OF False] by (simp add: default_af_entry_def)
    have upto: "[0..<Suc n] = 0 # [1..<Suc n]"
      using upt_rec[of 0 "Suc n"] by simp
    have active: "lp_active_entry (afs \<pi> (f,Suc n))"
      by (subst eq, subst upto, simp only: lp_active_entry.simps list_all_iff set_upt)
        auto
    show ?thesis by (rule lp_active_entry_sound[OF Argument_Filter.afs active])
  qed
qed

lemma lp_ground_filter:
  assumes "ground t"
  shows "ground (af_term \<pi> t)"
proof -
  show ?thesis using assms
  proof (induct t)
    case (Var x)
    then show ?case by simp
  next
    case (Fun f ts)
    have gr: "\<And>i. i < length ts \<Longrightarrow> ground (af_term \<pi> (ts!i))"
      using Fun by auto
    show ?case using Argument_Filter.afs[of "length ts" \<pi> f] gr
      by (cases "afs \<pi> (f,length ts)") (auto simp: set_conv_nth)
  qed
qed

definition lp_check_query where
  "lp_check_query \<pi> q n ground_positions = (case afs \<pi> (q,n) of
     AFList ps \<Rightarrow> list_all (\<lambda>i. i \<in> set ground_positions) ps
   | _ \<Rightarrow> False)"

lemma lp_check_query_sound:
  assumes ok: "lp_check_query \<pi> q n positions" and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "ground (af_term \<pi> (Fun q ts))"
proof -
  obtain ps where pi: "afs \<pi> (q,n) = AFList ps" and ps: "set ps \<subseteq> set positions"
    using ok unfolding lp_check_query_def by (cases "afs \<pi> (q,n)") (auto simp: list_all_iff)
  have bound: "set ps \<subseteq> {0..<n}"
    using Argument_Filter.afs[of n \<pi> q] by (auto simp: pi)
  have each: "\<And>i. i \<in> set ps \<Longrightarrow> ground (map (af_term \<pi>) ts ! i)"
  proof -
    fix i assume mem: "i \<in> set ps"
    have lt: "i<n" and required: "i \<in> set positions" using ps bound mem by auto
    have "ground (af_term \<pi> (ts!i))" by (rule lp_ground_filter[OF gr[OF required lt]])
    then show "ground (map (af_term \<pi>) ts ! i)" using lt len by simp
  qed
  show ?thesis using each by (simp add: len pi)
qed

definition check_lp_finite where
  "check_lp_finite I J P outs fallback names filters q n positions prf =
    (case afs_of filters of None \<Rightarrow> False | Some \<pi> \<Rightarrow>
      let out = (\<lambda>f. case map_of outs f of None \<Rightarrow> f | Some g \<Rightarrow> g);
          u = lp_u_lookup fallback names;
          R = lp_translation.translated P id out u;
          filtered = map (af_rule \<pi>) R
      in lp_check_active (fallback # concat names) \<pi> (map fst filters) \<and>
         lp_check_query \<pi> q n positions \<and>
         list_all (\<lambda>(l,r). vars_term r \<subseteq> vars_term l) filtered \<and>
         isOK (check_trs_termination_proof I J False id
           (tp_ops.mk I False [] filtered []) prf))"

theorem check_lp_finite_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_finite I J P outs fallback names filters q n positions prf"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ld P) {[(q,ts)]}"
proof -
  interpret tp_spec I by (rule I)
  obtain \<pi> where pi: "afs_of filters = Some \<pi>"
    using ok unfolding check_lp_finite_def by (cases "afs_of filters") auto
  let ?out = "\<lambda>f. case map_of outs f of None \<Rightarrow> f | Some g \<Rightarrow> g"
  let ?u = "lp_u_lookup fallback names"
  interpret lp_translation P id ?out ?u .
  have active: "lp_check_active (fallback # concat names) \<pi> (map fst filters)"
    and query: "lp_check_query \<pi> q n positions"
    and varlist: "list_all (\<lambda>(l,r). vars_term r \<subseteq> vars_term l) (map (af_rule \<pi>) translated)"
    and child: "isOK (check_trs_termination_proof I J False id
      (tp_ops.mk I False [] (map (af_rule \<pi>) translated) []) prf)"
    using ok by (auto simp: check_lp_finite_def pi Let_def)
  have vars: "\<And>l r. (l,r) \<in> af_rule \<pi> ` set translated \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  proof -
    fix l r assume mem: "(l,r) \<in> af_rule \<pi> ` set translated"
    have member: "(l,r) \<in> set (map (af_rule \<pi>) translated)" using mem by simp
    show "vars_term r \<subseteq> vars_term l"
      using bspec[OF varlist[unfolded list_all_iff] member] by simp
  qed
  have filter: "lp_filter \<pi> (range (\<lambda>(c,i). ?u c i))"
    by (rule lp_check_active_sound[OF _ active lp_u_range])
      (simp add: afs_of_Some_afs_syms[OF pi])
  have sn: "SN (rstep (af_rule \<pi> ` set translated))"
    using check_trs_termination_proof[OF I J child] by (simp add: SN_qrel_def)
  have ground: "ground (af_term \<pi> (encode (LPCall (q,ts))))"
    using lp_check_query_sound[OF query len gr] by (simp add: lp_tag_def)
  have machine: "SN_on (lp_machine P) {LPCall (q,ts)}"
    by (rule source_machine_terminates[OF filter sn vars ground])
  show ?thesis using lp_machine_implies_ld_termination[OF machine] by simp
qed

definition lp_atom_parser where
  "lp_atom_parser = xml_change (CPF_Input_Parser.term symbol_parser Mapping.empty)
    (\<lambda>t. case t of Fun f ts \<Rightarrow> xml_return (f,ts)
      | Var _ \<Rightarrow> xml_error (STR ''LP atom cannot be a variable''))"

definition lp_finite_parser where
  "lp_finite_parser = XMLdo (STR ''lpFiniteTerminationProof'') {
    P \<leftarrow> xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h \<leftarrow> xml_singleton (STR ''head'') lp_atom_parser id;
      bs \<leftarrow> xml_many (STR ''body'') lp_atom_parser id;
      xml_return (h,bs)
    }) id;
    outs \<leftarrow> xml_many (STR ''returns'')
      (xml_pair (STR ''return'') symbol_parser symbol_parser Pair) id;
    fallback \<leftarrow> xml_singleton (STR ''fallback'') symbol_parser id;
    names \<leftarrow> xml_many (STR ''continuations'')
      (xml_many (STR ''clause'') symbol_parser id) id;
    query \<leftarrow> XMLdo (STR ''query'') {
      q \<leftarrow> symbol_parser;
      n \<leftarrow> xml_nat (STR ''arity'');
      positions \<leftarrow> xml_many (STR ''ground'') (xml_nat (STR ''index'')) id;
      xml_return (q,n,positions)
    };
    filters \<leftarrow> CPF_Proof_Parser.afs symbol_parser;
    prf \<leftarrow> xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (P,outs,fallback,names,filters,query,prf)
  }"

definition check_lp_finite_xml where
  "check_lp_finite_xml xml = (case parse_xml_string lp_finite_parser xml of
    Right (P,outs,fallback,names,filters,(q,n,positions),prf) \<Rightarrow>
      check_lp_finite tp_rbt_impl dpp_rbt_impl P outs fallback names filters q n positions prf
    | _ \<Rightarrow> False)"

theorem check_lp_finite_xml_sound:
  assumes "parse_xml_string lp_finite_parser xml = Right (P,outs,fallback,names,filters,(q,n,positions),prf)"
    "check_lp_finite_xml xml" "length ts=n"
    "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ld P) {[(q,ts)]}"
  by (rule check_lp_finite_sound[OF tp_rbt_impl dpp_rbt_impl _ assms(3,4)])
    (use assms(1,2) in \<open>simp add: check_lp_finite_xml_def\<close>)

end
