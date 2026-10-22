theory LP_SEG_Residual_Check
  imports LP_SEG_Residual LP_SEG_Check LP_TOCL09_Checker
begin

definition lp_check_residual_branch where
  "lp_check_residual_branch fuel P Q node_count N V F i k anchor children c =
    (case lp_source_branch fuel k (N i@[(anchor,map Var (V i))]) (P!c) of
      None\<Rightarrow>False
    | Some None\<Rightarrow>children!c=None
    | Some (Some flat)\<Rightarrow>(case children!c of None\<Rightarrow>False | Some j\<Rightarrow>
        j<node_count \<and> flat\<noteq>[] \<and> fst (last flat)=anchor \<and> N j=butlast flat \<and>
        ((F i,snd (last flat)),[(F j,map Var (V j))])\<in>set Q))"

fun lp_check_residual_action where
  "lp_check_residual_action fuel P Q node_count N V F i LPSegSuccess =
    (N i=[] \<and> ((F i,map Var (V i)),[])\<in>set Q)"
| "lp_check_residual_action fuel P Q node_count N V F i (LPSegResolve k anchor children) =
    (N i\<noteq>[] \<and> lp_short_goals k (N i@[(anchor,map Var (V i))]) \<and>
     length children=length P \<and>
     list_all (lp_check_residual_branch fuel P Q node_count N V F i k anchor children) [0..<length P])"
| "lp_check_residual_action fuel P Q node_count N V F i (LPSegInstance j bindings) =
    (let subst=lp_seg_substitution bindings in
      j<node_count \<and> N i=map (\<lambda>a. lp_atom_subst a subst) (N j) \<and>
      ((F i,map Var (V i)),[(F j,map subst (V j))])\<in>set Q)"
| "lp_check_residual_action fuel P Q node_count N V F i (LPSegSplit a b) =
    (a<node_count \<and> b<node_count \<and> N i=N a@N b \<and>
      ((F i,map Var (V i)),[(F a,map Var (V a)),(F b,map Var (V b))])\<in>set Q)"

lemma lp_check_residual_action_sound:
  assumes checked: "lp_check_residual_action fuel P Q node_count N V F i action"
  shows "lp_seg_residual_valid P Q {0..<node_count} N V F i"
  using checked
proof (cases action)
  case LPSegSuccess then show ?thesis using checked
    by (auto intro: lp_seg_residual_valid.success)
next
  case (LPSegResolve k anchor children)
  have ne: "N i\<noteq>[]" and fresh: "lp_short_goals k (N i@[(anchor,map Var (V i))])"
    and branch: "\<And>c. c<length P \<Longrightarrow>
      lp_check_residual_branch fuel P Q node_count N V F i k anchor children c"
    using checked LPSegResolve by (auto simp: list_all_iff)
  have total: "\<forall>c<length P. \<exists>result.
    lp_source_branch fuel k (N i@[(anchor,map Var (V i))]) (P!c)=Some result"
  proof (intro allI impI)
    fix c assume c: "c<length P"
    show "\<exists>result. lp_source_branch fuel k (N i@[(anchor,map Var (V i))]) (P!c)=Some result"
      using branch[OF c] unfolding lp_check_residual_branch_def
      by (cases "lp_source_branch fuel k (N i@[(anchor,map Var (V i))]) (P!c)") auto
  qed
  have covered: "\<forall>c<length P. \<forall>child inputs.
    lp_source_branch fuel k (N i@[(anchor,map Var (V i))]) (P!c)=
      Some (Some (child@[(anchor,inputs)])) \<longrightarrow>
    (\<exists>j\<in>{0..<node_count}. N j=child \<and>
      ((F i,inputs),[(F j,map Var (V j))])\<in>set Q)"
  proof (intro allI impI)
    fix c child inputs
    assume c: "c<length P" and result:
      "lp_source_branch fuel k (N i@[(anchor,map Var (V i))]) (P!c)=Some (Some (child@[(anchor,inputs)]))"
    show "\<exists>j\<in>{0..<node_count}. N j=child \<and>
      ((F i,inputs),[(F j,map Var (V j))])\<in>set Q"
      using branch[OF c] unfolding lp_check_residual_branch_def result
      by (auto split: option.splits)
  qed
  show ?thesis by (rule lp_seg_residual_valid.resolve[OF ne fresh total covered])
next
  case (LPSegInstance j bindings)
  show ?thesis using checked LPSegInstance
    by (auto simp: Let_def intro: lp_seg_residual_valid.inst)
next
  case (LPSegSplit a b)
  show ?thesis using checked LPSegSplit by (auto intro: lp_seg_residual_valid.split)
qed

text \<open>The interface list below is the complete residual predicate
  interface, not a groundness assertion.\<close>

type_synonym 'f lp_residual_node =
  "('f,string) lp_atom list \<times> string list \<times> 'f \<times> 'f lp_seg_action"

definition lp_residual_goals where "lp_residual_goals nds i = fst (nds!i)"
definition lp_residual_vars where "lp_residual_vars nds i = fst (snd (nds!i))"
definition lp_residual_symbol where "lp_residual_symbol nds i = fst (snd (snd (nds!i)))"
definition lp_residual_action where "lp_residual_action nds i = snd (snd (snd (nds!i)))"

definition lp_check_residual_graph where
  "lp_check_residual_graph fuel P Q nds root_id =
    (root_id<length nds \<and>
     list_all (\<lambda>i. lp_check_residual_action fuel P Q (length nds)
       (lp_residual_goals nds) (lp_residual_vars nds) (lp_residual_symbol nds)
       i (lp_residual_action nds i)) [0..<length nds])"

theorem lp_check_residual_graph_sound:
  fixes P Q :: "('f,string) lp_clause list"
    and nds :: "'f lp_residual_node list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lp_check_residual_graph fuel P Q nds root_id"
    and sn: "SN_on (lp_ild Q) {[(lp_residual_symbol nds root_id,map \<rho> (lp_residual_vars nds root_id))]}"
  shows "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) (lp_residual_goals nds root_id)}"
proof -
  have member: "root_id\<in>{0..<length nds}"
    using checked by (simp add: lp_check_residual_graph_def)
  have valid: "\<And>i. i\<in>{0..<length nds} \<Longrightarrow>
    lp_seg_residual_valid P Q {0..<length nds} (lp_residual_goals nds)
      (lp_residual_vars nds) (lp_residual_symbol nds) i"
    by (rule lp_check_residual_action_sound)
      (use checked in \<open>auto simp: lp_check_residual_graph_def list_all_iff\<close>)
  have rep: "lp_seg_represents {0..<length nds} (lp_residual_goals nds)
    (lp_residual_vars nds) (lp_residual_symbol nds)
    [(lp_residual_symbol nds root_id,map \<rho> (lp_residual_vars nds root_id))]
    (map (\<lambda>a. lp_atom_eval a \<rho>) (lp_residual_goals nds root_id))"
    using lp_seg_represents.cons[OF member lp_seg_represents.empty, where \<rho>=\<rho>]
    by simp
  show ?thesis by (rule lp_seg_residual_termination[OF valid sn rep])
qed

definition check_lp_residual where
  "check_lp_residual I J fuel P nds root_id q n positions Q outs fallback names filters q' prf =
    (lp_check_residual_graph fuel P Q nds root_id \<and>
     lp_residual_goals nds root_id=[(q,map Var (lp_source_query_args n))] \<and>
     lp_residual_vars nds root_id=lp_source_query_args n \<and>
     lp_residual_symbol nds root_id=q' \<and>
     check_lp_finite I J Q outs fallback names filters q' n positions prf)"

theorem check_lp_residual_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_residual I J fuel P nds root_id q n positions Q outs fallback names filters q' prf"
    and len: "length ts=n"
    and ground: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  let ?vals = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  let ?rho = "\<lambda>x. ?vals!(length x-1)"
  have child: "check_lp_finite I J Q outs fallback names filters q' n positions prf"
    using ok by (simp add: check_lp_residual_def)
  have sn: "SN_on (lp_ild Q) {[(q',?vals)]}"
    by (rule check_lp_tocl09_sound[OF I J child len ground])
  have eval: "map ?rho (lp_source_query_args n)=?vals"
    using lp_source_query_eval[of ?vals] len by simp
  have source: "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a ?rho) (lp_residual_goals nds root_id)}"
    by (rule lp_check_residual_graph_sound)
      (use ok sn eval in \<open>auto simp: check_lp_residual_def\<close>)
  show ?thesis using source ok eval
    by (simp add: check_lp_residual_def lp_atom_eval_def o_def)
qed

end
