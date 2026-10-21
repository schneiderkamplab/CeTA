theory LP_SEG_Graph
  imports LP_SEG_Expansion
begin

text \<open>Cyclic symbolic graphs are justified by a separate finite TRS.
  No back edge is a success leaf. Full termination of the extracted TRS is
  required here; innermost termination is not silently substituted for it.\<close>

lemma lp_seg_resolve_decrease:
  fixes P :: "('f,string) lp_clause list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes fresh: "lp_short_goals k (gs @ [(anchor,map Var G)])"
    and short: "\<forall>x\<in>set G. length x<k"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<rho> x)"
    and total: "\<And>c. c<length P \<Longrightarrow> \<exists>result.
      lp_source_branch fuel k (gs @ [(anchor,map Var G)]) (P!c)=Some result"
    and covered: "\<And>c child inputs. c<length P \<Longrightarrow>
      lp_source_branch fuel k (gs @ [(anchor,map Var G)]) (P!c)=
        Some (Some (child @ [(anchor,inputs)])) \<Longrightarrow>
      \<exists>j. j\<in>I \<and> N j=child \<and>
        set (H j)\<subseteq>\<Union>(vars_term ` set inputs) \<and>
        (Fun f inputs,Fun (F j) (map Var (H j)))\<in>R"
    and measured: "lp_seg_measure f G \<rho> t"
    and step: "(map (\<lambda>a. lp_atom_eval a \<rho>) gs,hs)\<in>lp_ild P"
  shows "\<exists>j \<eta> u. j\<in>I \<and> (t,u)\<in>rstep R \<and>
    lp_seg_measure (F j) (H j) \<eta> u \<and>
    (\<forall>x\<in>set (H j). lp_seg_ground (\<eta> x)) \<and>
    map (\<lambda>a. lp_atom_eval a \<eta>) (N j)=hs"
proof -
  obtain c child inputs \<eta> where c: "c<length P"
    and branch: "lp_source_branch fuel k (gs @ [(anchor,map Var G)]) (P!c)=
      Some (Some (child @ [(anchor,inputs)]))"
    and child: "map (\<lambda>a. lp_atom_eval a \<eta>) child=hs"
    and inputs: "map (\<lambda>s. lp_ieval s \<eta>) inputs=map \<rho> G"
    and finite: "\<forall>x\<in>\<Union>(vars_term ` set inputs). lp_seg_ground (\<eta> x)"
    by (rule lp_seg_measured_expansion[OF fresh short ground total step]) blast
  obtain j where j: "j\<in>I" and node: "N j=child"
    and vars: "set (H j)\<subseteq>\<Union>(vars_term ` set inputs)"
    and edge: "(Fun f inputs,Fun (F j) (map Var (H j)))\<in>R"
    using covered[OF c branch] by blast
  have output_eq: "map (\<lambda>s. lp_ieval s \<eta>) (map Var (H j))=map \<eta> (H j)"
    by simp
  have output_vars: "\<Union>(vars_term ` set (map Var (H j)))\<subseteq>
    \<Union>(vars_term ` set inputs)" using vars by simp
  obtain u where u: "(t,u)\<in>rstep R"
    and measure: "lp_seg_measure (F j) (H j) \<eta> u"
    using lp_seg_rewrite_measure[OF measured edge inputs output_eq finite output_vars]
    by (elim exE conjE) assumption
  have child_ground: "\<forall>x\<in>set (H j). lp_seg_ground (\<eta> x)"
    using finite vars by auto
  show ?thesis
    by (rule exI[of _ j], rule exI[of _ \<eta>], rule exI[of _ u])
      (use j u measure child_ground node child in simp)
qed

lemma lp_seg_instance_decrease:
  fixes \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
    and \<mu> :: "string \<Rightarrow> ('f,string) term"
    and G H :: "string list"
  assumes measured: "lp_seg_measure f G \<rho> t"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<rho> x)"
    and vars: "\<forall>x\<in>set H. vars_term (\<mu> x) \<subseteq> set G"
    and edge: "(Fun f (map Var G),Fun g (map \<mu> H))\<in>R"
  shows "\<exists>u. (t,u)\<in>rstep R \<and>
    lp_seg_measure g H (\<lambda>x. lp_ieval (\<mu> x) \<rho>) u \<and>
    (\<forall>x\<in>set H. lp_seg_ground (lp_ieval (\<mu> x) \<rho>))"
proof -
  have finite: "\<forall>x\<in>\<Union>(vars_term ` set (map Var G)). lp_seg_ground (\<rho> x)"
    using ground by auto
  have subset: "\<Union>(vars_term ` set (map \<mu> H))\<subseteq>
    \<Union>(vars_term ` set (map Var G))" using vars by auto
  have inp: "map (\<lambda>s. lp_ieval s \<rho>) (map Var G)=map \<rho> G" by simp
  have outp: "map (\<lambda>s. lp_ieval s \<rho>) (map \<mu> H)=
    map (\<lambda>x. lp_ieval (\<mu> x) \<rho>) H" by (simp add: o_def)
  obtain u where u: "(t,u)\<in>rstep R" and target:
    "lp_seg_measure g H (\<lambda>x. lp_ieval (\<mu> x) \<rho>) u"
    using lp_seg_rewrite_measure[OF measured edge inp outp finite subset]
    by (elim exE conjE) assumption
  have "\<forall>x\<in>set H. lp_seg_ground (lp_ieval (\<mu> x) \<rho>)"
    using ground vars by (auto simp: lp_seg_ground_eval)
  then show ?thesis using u target by blast
qed

lemma lp_seg_projection_decrease:
  fixes \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes measured: "lp_seg_measure f G \<rho> t"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<rho> x)"
    and subset: "set H \<subseteq> set G"
    and edge: "(Fun f (map Var G),Fun g (map Var H))\<in>R"
  shows "\<exists>u. (t,u)\<in>rstep R \<and> lp_seg_measure g H \<rho> u \<and>
    (\<forall>x\<in>set H. lp_seg_ground (\<rho> x))"
  using lp_seg_instance_decrease[OF measured ground _ edge]
    subset by (simp add: subset_iff)

inductive lp_seg_node_valid
  for P :: "('f,string) lp_clause list"
    and I :: "nat set"
    and N :: "nat \<Rightarrow> ('f,string) lp_atom list"
    and G :: "nat \<Rightarrow> string list"
    and F :: "nat \<Rightarrow> 'f"
    and R :: "('f,string) trs"
  where
  success: "N i=[] \<Longrightarrow> lp_seg_node_valid P I N G F R i"
| resolve: "lp_short_goals k (N i @ [(anchor,map Var (G i))]) \<Longrightarrow>
    (\<forall>x\<in>set (G i). length x<k) \<Longrightarrow>
    (\<forall>c<length P. \<exists>result.
      lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)=Some result) \<Longrightarrow>
    (\<forall>c<length P. \<forall>child inputs.
      lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)=
        Some (Some (child @ [(anchor,inputs)])) \<longrightarrow>
      (\<exists>j\<in>I. N j=child \<and> set (G j)\<subseteq>\<Union>(vars_term ` set inputs) \<and>
        (Fun (F i) inputs,Fun (F j) (map Var (G j)))\<in>R)) \<Longrightarrow>
    lp_seg_node_valid P I N G F R i"
| inst: "j\<in>I \<Longrightarrow> N i=map (\<lambda>a. lp_atom_subst a \<mu>) (N j) \<Longrightarrow>
    (\<forall>x\<in>set (G j). vars_term (\<mu> x) \<subseteq> set (G i)) \<Longrightarrow>
    (Fun (F i) (map Var (G i)),Fun (F j) (map \<mu> (G j)))\<in>R \<Longrightarrow>
    lp_seg_node_valid P I N G F R i"
| split: "a\<in>I \<Longrightarrow> b\<in>I \<Longrightarrow> N i=N a @ N b \<Longrightarrow>
    set (G a) \<subseteq> set (G i) \<Longrightarrow> set (G b) \<subseteq> set (G i) \<Longrightarrow>
    (Fun (F i) (map Var (G i)),Fun (F a) (map Var (G a)))\<in>R \<Longrightarrow>
    (Fun (F i) (map Var (G i)),Fun (F b) (map Var (G b)))\<in>R \<Longrightarrow>
    lp_seg_node_valid P I N G F R i"

lemma lp_seg_node_sound:
  assumes valid: "lp_seg_node_valid P I N G F R i"
    and measured: "lp_seg_measure (F i) (G i) \<rho> t"
    and ground: "\<forall>x\<in>set (G i). lp_seg_ground (\<rho> x)"
    and ih: "\<And>j \<eta> u. j\<in>I \<Longrightarrow> (t,u)\<in>rstep R \<Longrightarrow>
      lp_seg_measure (F j) (G j) \<eta> u \<Longrightarrow>
      (\<forall>x\<in>set (G j). lp_seg_ground (\<eta> x)) \<Longrightarrow>
      SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) (N j)}"
  shows "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) (N i)}"
  using valid
proof cases
  case success
  show ?thesis using lp_symbolic_empty[of P]
    unfolding success lp_symbolic_sn_def by simp
next
  case (resolve k anchor fuel)
  show ?thesis
  proof (rule step_reflects_SN_on)
    fix hs assume step: "(map (\<lambda>a. lp_atom_eval a \<rho>) (N i),hs)\<in>lp_ild P"
    have total: "\<And>c. c<length P \<Longrightarrow> \<exists>result.
      lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)=Some result"
      using resolve(3) by auto
    have covered: "\<And>c child inputs. c<length P \<Longrightarrow>
      lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)=
        Some (Some (child @ [(anchor,inputs)])) \<Longrightarrow>
      \<exists>j. j\<in>I \<and> N j=child \<and>
        set (G j)\<subseteq>\<Union>(vars_term ` set inputs) \<and>
        (Fun (F i) inputs,Fun (F j) (map Var (G j)))\<in>R"
      using resolve(4) by blast
    have decrease: "\<exists>j \<eta> u. j\<in>I \<and> (t,u)\<in>rstep R \<and>
      lp_seg_measure (F j) (G j) \<eta> u \<and>
      (\<forall>x\<in>set (G j). lp_seg_ground (\<eta> x)) \<and>
      map (\<lambda>a. lp_atom_eval a \<eta>) (N j)=hs"
      by (rule lp_seg_resolve_decrease[OF resolve(1,2) ground _ _ measured step])
        (use total covered in blast)+
    obtain j \<eta> u where j: "j\<in>I" and edge: "(t,u)\<in>rstep R"
      and target: "lp_seg_measure (F j) (G j) \<eta> u"
      and finite: "\<forall>x\<in>set (G j). lp_seg_ground (\<eta> x)"
      and goals: "map (\<lambda>a. lp_atom_eval a \<eta>) (N j)=hs"
      using decrease
      by (elim exE conjE) assumption
    show "SN_on (lp_ild P) {hs}" using ih[OF j edge target finite] goals by simp
  qed
next
  case (inst j \<mu>)
  obtain u where edge: "(t,u)\<in>rstep R"
    and target: "lp_seg_measure (F j) (G j) (\<lambda>x. lp_ieval (\<mu> x) \<rho>) u"
    and finite: "\<forall>x\<in>set (G j). lp_seg_ground (lp_ieval (\<mu> x) \<rho>)"
    using lp_seg_instance_decrease[OF measured ground inst(3,4)]
    by (elim exE conjE) assumption
  show ?thesis using ih[OF inst(1) edge target finite]
    by (simp add: inst(2) lp_atom_eval_finite_subst o_def)
next
  case (split a b)
  obtain u where edge_a: "(t,u)\<in>rstep R"
    and target_a: "lp_seg_measure (F a) (G a) \<rho> u"
    and finite_a: "\<forall>x\<in>set (G a). lp_seg_ground (\<rho> x)"
    using lp_seg_projection_decrease[OF measured ground split(4,6)]
    by (elim exE conjE) assumption
  have first: "SN_on (lp_ild P) {map (\<lambda>v. lp_atom_eval v \<rho>) (N a)}"
    by (rule ih[OF split(1) edge_a target_a finite_a])
  let ?K = "\<lambda>\<eta>. (\<forall>x\<in>set (G i). lp_seg_ground (\<eta> x)) \<and>
    map \<eta> (G i)=map \<rho> (G i)"
  have suffix: "\<And>\<eta>. ?K \<eta> \<Longrightarrow>
    SN_on (lp_ild P) {map (\<lambda>v. lp_atom_eval v \<eta>) (N b)}"
  proof -
    fix \<eta> assume k: "?K \<eta>"
    have same: "lp_seg_measure (F i) (G i) \<eta> t"
      using measured k unfolding lp_seg_measure_def by simp
    have finite: "\<forall>x\<in>set (G i). lp_seg_ground (\<eta> x)" by (rule conjunct1[OF k])
    obtain v where edge_b: "(t,v)\<in>rstep R"
      and target_b: "lp_seg_measure (F b) (G b) \<eta> v"
      and finite_b: "\<forall>x\<in>set (G b). lp_seg_ground (\<eta> x)"
      using lp_seg_projection_decrease[OF same finite split(5,7)]
      by (elim exE conjE) assumption
    show "SN_on (lp_ild P) {map (\<lambda>v. lp_atom_eval v \<eta>) (N b)}"
      by (rule ih[OF split(2) edge_b target_b finite_b])
  qed
  have stable: "\<And>\<eta> \<sigma>. ?K \<eta> \<Longrightarrow> ?K (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
    by (elim conjE, rule lp_seg_fixed_ground_stable) assumption+
  have initial: "?K \<rho>" using ground by simp
  show ?thesis unfolding split(3) map_append
    by (rule lp_seg_append_sn_invariant[OF first suffix stable initial])
qed

theorem lp_seg_graph_terminates:
  fixes P :: "('f,string) lp_clause list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes sn: "SN (rstep R)"
    and valid: "\<And>i. i\<in>I \<Longrightarrow> lp_seg_node_valid P I N G F R i"
    and member: "i\<in>I"
    and ground: "\<forall>x\<in>set (G i). lp_seg_ground (\<rho> x)"
  shows "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) (N i)}"
proof -
  obtain t where measured: "lp_seg_measure (F i) (G i) \<rho> t"
    using lp_seg_measure_exists[OF ground, of "F i"] by (elim exE) assumption
  have all: "\<forall>i \<rho>. i\<in>I \<longrightarrow> lp_seg_measure (F i) (G i) \<rho> t \<longrightarrow>
    (\<forall>x\<in>set (G i). lp_seg_ground (\<rho> x)) \<longrightarrow>
    SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) (N i)}"
  proof (rule SN_on_induct[OF sn UNIV_I])
    fix t :: "('f,string) term"
    assume ih: "\<And>u. (t,u)\<in>rstep R \<Longrightarrow>
      \<forall>i \<rho>. i\<in>I \<longrightarrow> lp_seg_measure (F i) (G i) \<rho> u \<longrightarrow>
      (\<forall>x\<in>set (G i). lp_seg_ground (\<rho> x)) \<longrightarrow>
      SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) (N i)}"
    show "\<forall>i \<rho>. i\<in>I \<longrightarrow> lp_seg_measure (F i) (G i) \<rho> t \<longrightarrow>
      (\<forall>x\<in>set (G i). lp_seg_ground (\<rho> x)) \<longrightarrow>
      SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) (N i)}"
    proof (intro allI impI)
      fix j :: nat and \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
      assume j: "j\<in>I" and measure: "lp_seg_measure (F j) (G j) \<eta> t"
        and finite: "\<forall>x\<in>set (G j). lp_seg_ground (\<eta> x)"
      show "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) (N j)}"
        by (rule lp_seg_node_sound[OF valid[OF j] measure finite]) (use ih in blast)
    qed
  qed
  show ?thesis using all member measured ground by blast
qed

end
