theory LP_Source_Graph
  imports LP_Symbolic_Evaluation
begin

text \<open>Acyclic region checker for symbolic evaluation graphs. Nodes are
  independently addressed and shared. This is not the cyclic graph-to-TRS
  theorem: an unresolved back-edge is rejected, never counted as a proof.\<close>

type_synonym 'f lp_source_node =
  "('f,string) lp_atom list \<times> nat \<times> nat option list"

definition lp_check_source_node where
  "lp_check_source_node fuel P nds i =
    (let (gs,k,children)=nds!i in
      if gs=[] then children=[] else lp_short_goals k gs \<and> length children=length P \<and>
      list_all (\<lambda>c. case lp_source_branch fuel k gs (P!c) of
        None\<Rightarrow>False
      | Some None\<Rightarrow>children!c=None
      | Some (Some hs)\<Rightarrow>(case children!c of None\<Rightarrow>False | Some j\<Rightarrow>
          j<i \<and> fst (nds!j)=hs)) [0..<length P])"

definition lp_check_source_graph where
  "lp_check_source_graph fuel P nds root_id =
    (root_id<length nds \<and> list_all (lp_check_source_node fuel P nds) [0..<length nds])"

theorem lp_check_source_graph_sound:
  assumes checked: "lp_check_source_graph fuel P nds root_id"
  shows "lp_symbolic_sn P (fst (nds!root_id))"
proof -
  have each: "\<And>i. i<length nds \<Longrightarrow> lp_symbolic_sn P (fst (nds!i))"
  proof -
    fix i show "i<length nds \<Longrightarrow> lp_symbolic_sn P (fst (nds!i))"
    proof (induct i rule: less_induct)
      case (less i)
      obtain gs k children where node: "nds!i=(gs,k,children)" by (cases "nds!i") auto
      have ok: "lp_check_source_node fuel P nds i"
        using checked less.prems by (auto simp: lp_check_source_graph_def list_all_iff)
      show ?case
      proof (cases "gs=[]")
        case True then show ?thesis by (simp add: node lp_symbolic_empty)
      next
        case False
        have fresh: "lp_short_goals k gs" and len: "length children=length P"
          and branches: "\<And>c. c<length P \<Longrightarrow>
            (case lp_source_branch fuel k gs (P!c) of
              None\<Rightarrow>False | Some None\<Rightarrow>children!c=None |
              Some (Some hs)\<Rightarrow>(case children!c of None\<Rightarrow>False | Some j\<Rightarrow>
                j<i \<and> fst (nds!j)=hs))"
          using ok by (auto simp: lp_check_source_node_def node False Let_def list_all_iff)
        have "lp_symbolic_sn P gs"
        proof (rule lp_symbolic_resolve[OF fresh _ False])
          fix clause assume "clause\<in>set P"
          then obtain c where c: "c<length P" "P!c=clause" by (auto simp: in_set_conv_nth)
          show "\<exists>result. lp_source_branch fuel k gs clause=Some result \<and>
            (\<forall>hs. result=Some hs \<longrightarrow> lp_symbolic_sn P hs)"
            using branches[OF c(1)] less.hyps less.prems
            by (cases "lp_source_branch fuel k gs clause"; cases "children!c")
              (auto simp: c(2) split: option.splits)
        qed
        then show ?thesis by (simp add: node)
      qed
    qed
  qed
  show ?thesis using each checked by (auto simp: lp_check_source_graph_def)
qed

definition lp_source_query_args where
  "lp_source_query_args n = map (\<lambda>i. replicate (Suc i) (CHR ''$'')) [0..<n]"

lemma lp_source_query_eval:
  "map (\<lambda>x. lp_ieval (Var x) (\<lambda>x. ts!(length x - 1)))
    (lp_source_query_args (length ts)) = ts"
  by (auto simp: lp_source_query_args_def map_map intro!: nth_equalityI)

theorem lp_source_graph_query_sound:
  fixes P :: "('f,string) lp_clause list" and ts :: "('f,string) lp_iterm list"
  assumes checked: "lp_check_source_graph fuel P nds root_id"
    and initial: "fst (nds!root_id)=[(q,map Var (lp_source_query_args n))]"
    and len: "length ts=n"
  shows "SN_on (lp_ild P) {[(q,ts :: ('f,string) lp_iterm list)]}"
proof -
  have sn: "lp_symbolic_sn P [(q,map Var (lp_source_query_args n))]"
    using lp_check_source_graph_sound[OF checked] initial by simp
  have eval: "map (\<lambda>x. ts!(length x - 1)) (lp_source_query_args n) = ts"
    using lp_source_query_eval[of ts] len by simp
  have evaluated: "map (\<lambda>a. lp_atom_eval a (\<lambda>x. ts!(length x - 1)))
    [(q,map Var (lp_source_query_args n))] = [(q,ts)]"
    by (simp only: lp_atom_eval_def fst_conv snd_conv list.map map_map o_def lp_ieval.simps eval)
  have "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a (\<lambda>x. ts!(length x - 1)))
    [(q,map Var (lp_source_query_args n))]}"
    using sn[unfolded lp_symbolic_sn_def] by (rule spec)
  then show ?thesis by (simp only: evaluated)
qed

end
