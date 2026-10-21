theory LP_SEG_Check
  imports LP_SEG_Graph LP_Source_Graph
begin

datatype 'f lp_seg_action =
    LPSegSuccess
  | LPSegResolve nat 'f "nat option list"
  | LPSegInstance nat "(string \<times> ('f,string) term) list"
  | LPSegSplit nat nat

definition lp_seg_substitution where
  "lp_seg_substitution bindings x = (case map_of bindings x of None\<Rightarrow>Var x | Some t\<Rightarrow>t)"

definition lp_check_seg_branch where
  "lp_check_seg_branch fuel P node_count N G F trs_rules i k anchor children c =
    (case lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c) of
      None\<Rightarrow>False
    | Some None\<Rightarrow>children!c=None
    | Some (Some flat)\<Rightarrow>(case children!c of None\<Rightarrow>False | Some j\<Rightarrow>
        j<node_count \<and> flat\<noteq>[] \<and> fst (last flat)=anchor \<and> N j=butlast flat \<and>
        set (G j) \<subseteq> \<Union>(vars_term ` set (snd (last flat))) \<and>
        (Fun (F i) (snd (last flat)),Fun (F j) (map Var (G j)))\<in>set trs_rules))"

fun lp_check_seg_action where
  "lp_check_seg_action fuel P node_count N G F trs_rules i LPSegSuccess = (N i=[])"
| "lp_check_seg_action fuel P node_count N G F trs_rules i (LPSegResolve k anchor children) =
    (lp_short_goals k (N i @ [(anchor,map Var (G i))]) \<and>
     list_all (\<lambda>x. length x<k) (G i) \<and> length children=length P \<and>
     list_all (lp_check_seg_branch fuel P node_count N G F trs_rules i k anchor children) [0..<length P])"
| "lp_check_seg_action fuel P node_count N G F trs_rules i (LPSegInstance j bindings) =
    (let subst=lp_seg_substitution bindings in
      j<node_count \<and> N i=map (\<lambda>a. lp_atom_subst a subst) (N j) \<and>
      list_all (\<lambda>x. vars_term (subst x) \<subseteq> set (G i)) (G j) \<and>
      (Fun (F i) (map Var (G i)),Fun (F j) (map subst (G j)))\<in>set trs_rules)"
| "lp_check_seg_action fuel P node_count N G F trs_rules i (LPSegSplit a b) =
    (a<node_count \<and> b<node_count \<and> N i=N a @ N b \<and>
     set (G a) \<subseteq> set (G i) \<and> set (G b) \<subseteq> set (G i) \<and>
     (Fun (F i) (map Var (G i)),Fun (F a) (map Var (G a)))\<in>set trs_rules \<and>
     (Fun (F i) (map Var (G i)),Fun (F b) (map Var (G b)))\<in>set trs_rules)"

lemma lp_check_seg_action_sound:
  assumes checked: "lp_check_seg_action fuel P node_count N G F trs_rules i action"
  shows "lp_seg_node_valid P {0..<node_count} N G F (set trs_rules) i"
  using checked
proof (cases action)
  case LPSegSuccess then show ?thesis using checked
    by (auto intro: lp_seg_node_valid.success)
next
  case (LPSegResolve k anchor children)
  have fresh: "lp_short_goals k (N i @ [(anchor,map Var (G i))])"
    and short: "\<forall>x\<in>set (G i). length x<k"
    and branch: "\<And>c. c<length P \<Longrightarrow>
      lp_check_seg_branch fuel P node_count N G F trs_rules i k anchor children c"
    using checked LPSegResolve by (auto simp: list_all_iff)
  have total: "\<forall>c<length P. \<exists>result.
    lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)=Some result"
  proof (intro allI impI)
    fix c assume c: "c<length P"
    show "\<exists>result. lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)=Some result"
      using branch[OF c] unfolding lp_check_seg_branch_def
      by (cases "lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)") auto
  qed
  have covered: "\<forall>c<length P. \<forall>child inputs.
    lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)=
      Some (Some (child @ [(anchor,inputs)])) \<longrightarrow>
    (\<exists>j\<in>{0..<node_count}. N j=child \<and> set (G j) \<subseteq> \<Union>(vars_term ` set inputs) \<and>
      (Fun (F i) inputs,Fun (F j) (map Var (G j)))\<in>set trs_rules)"
  proof (intro allI impI)
    fix c child inputs
    assume c: "c<length P" and result:
      "lp_source_branch fuel k (N i @ [(anchor,map Var (G i))]) (P!c)=
        Some (Some (child @ [(anchor,inputs)]))"
    show "\<exists>j\<in>{0..<node_count}. N j=child \<and> set (G j) \<subseteq> \<Union>(vars_term ` set inputs) \<and>
      (Fun (F i) inputs,Fun (F j) (map Var (G j)))\<in>set trs_rules"
      using branch[OF c] unfolding lp_check_seg_branch_def result
      by (auto split: option.splits)
  qed
  show ?thesis by (rule lp_seg_node_valid.resolve[OF fresh short total covered])
next
  case (LPSegInstance j bindings)
  show ?thesis using checked LPSegInstance
    by (auto simp: Let_def list_all_iff intro: lp_seg_node_valid.inst)
next
  case (LPSegSplit a b)
  show ?thesis using checked LPSegSplit by (auto intro: lp_seg_node_valid.split)
qed

type_synonym 'f lp_seg_node =
  "('f,string) lp_atom list \<times> string list \<times> 'f \<times> 'f lp_seg_action"

definition lp_seg_node_goals where "lp_seg_node_goals nds i = fst (nds!i)"
definition lp_seg_node_ground where "lp_seg_node_ground nds i = fst (snd (nds!i))"
definition lp_seg_node_symbol where "lp_seg_node_symbol nds i = fst (snd (snd (nds!i)))"
definition lp_seg_node_action where "lp_seg_node_action nds i = snd (snd (snd (nds!i)))"

definition lp_check_seg_graph where
  "lp_check_seg_graph fuel P nds trs_rules root_id =
    (root_id<length nds \<and>
      list_all (\<lambda>i. lp_check_seg_action fuel P (length nds)
        (lp_seg_node_goals nds) (lp_seg_node_ground nds) (lp_seg_node_symbol nds)
        trs_rules i (lp_seg_node_action nds i)) [0..<length nds])"

theorem lp_check_seg_graph_sound:
  fixes P :: "('f,string) lp_clause list"
    and nds :: "'f lp_seg_node list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lp_check_seg_graph fuel P nds trs_rules root_id"
    and sn: "SN (rstep (set trs_rules))"
    and ground: "\<forall>x\<in>set (lp_seg_node_ground nds root_id). lp_seg_ground (\<rho> x)"
  shows "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) (lp_seg_node_goals nds root_id)}"
proof -
  have member: "root_id\<in>{0..<length nds}"
    using checked by (simp add: lp_check_seg_graph_def)
  have valid: "\<And>i. i\<in>{0..<length nds} \<Longrightarrow>
    lp_seg_node_valid P {0..<length nds} (lp_seg_node_goals nds)
      (lp_seg_node_ground nds) (lp_seg_node_symbol nds) (set trs_rules) i"
    by (rule lp_check_seg_action_sound)
      (use checked in \<open>auto simp: lp_check_seg_graph_def list_all_iff\<close>)
  show ?thesis
    by (rule lp_seg_graph_terminates[where I="{0..<length nds}"
      and G="lp_seg_node_ground nds" and F="lp_seg_node_symbol nds"
      and R="set trs_rules", OF sn _ member ground]) (rule valid)
qed

theorem lp_seg_query_sound:
  fixes P :: "('f,string) lp_clause list"
    and nds :: "'f lp_seg_node list"
    and ts :: "('f,string) lp_iterm list"
  assumes checked: "lp_check_seg_graph fuel P nds trs_rules root_id"
    and sn: "SN (rstep (set trs_rules))"
    and initial: "lp_seg_node_goals nds root_id=[(q,map Var (lp_source_query_args n))]"
    and mode: "lp_seg_node_ground nds root_id=map (\<lambda>i. lp_source_query_args n ! i) positions"
    and positions: "\<forall>i\<in>set positions. i<n"
    and len: "length ts=n"
    and ground: "\<forall>i\<in>set positions. lp_seg_ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,ts)]}"
proof -
  let ?\<rho> = "\<lambda>x. ts!(length x - 1)"
  have finite: "\<forall>x\<in>set (lp_seg_node_ground nds root_id). lp_seg_ground (?\<rho> x)"
    using positions ground by (auto simp: mode lp_source_query_args_def)
  have eval: "map ?\<rho> (lp_source_query_args n)=ts"
    using lp_source_query_eval[of ts] len by simp
  have sn_source: "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a ?\<rho>) (lp_seg_node_goals nds root_id)}"
    by (rule lp_check_seg_graph_sound[OF checked sn finite])
  show ?thesis using sn_source
    by (simp only: initial lp_atom_eval_def fst_conv snd_conv list.map map_map o_def lp_ieval.simps eval)
qed

end
