theory LP_Rational_Graph_Match
  imports LP_Rational_Closed_Graph
begin

fun lp_rational_match where
  "lp_rational_match 0 G env t i = False"
| "lp_rational_match (Suc fuel) G env (Var x) i =
    (i<length G \<and> map_of env x=Some i)"
| "lp_rational_match (Suc fuel) G env (Fun f ts) i =
    (i<length G \<and> (case G!i of LPRExternal x \<Rightarrow> False
      | LPRBranch g js \<Rightarrow> f=g \<and> length ts=length js \<and>
        list_all (\<lambda>k. lp_rational_match fuel G env (ts!k) (js!k)) [0..<length ts]))"

definition lp_rational_match_env where
  "lp_rational_match_env G rho env x =
    (case map_of env x of None \<Rightarrow> rho x
      | Some i \<Rightarrow> lp_rational_graph_value G rho i)"

lemma lp_rational_match_sound:
  assumes "lp_rational_match fuel G env t i"
  shows "lp_ieval t (lp_rational_match_env G rho env)=lp_rational_graph_value G rho i"
  using assms
proof (induction fuel arbitrary: t i)
  case 0 then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases t)
    case (Var x)
    with Suc.prems show ?thesis by (simp add: lp_rational_match_env_def)
  next
    case (Fun f ts)
    obtain js where branch: "G!i=LPRBranch f js" and lengths: "length ts=length js"
      and children: "\<And>k. k<length ts \<Longrightarrow> lp_rational_match fuel G env (ts!k) (js!k)"
      and index: "i<length G"
      using Suc.prems Fun by (auto simp: list_all_iff split: lp_rational_node.splits)
    have root: "lp_rational_graph_value G rho i=LPIFun f (map (lp_rational_graph_value G rho) js)"
      by (rule lp_rational_graph_branch[OF lp_rational_graph_value_model index branch])
    have lists: "map (\<lambda>t. lp_ieval t (lp_rational_match_env G rho env)) ts =
      map (lp_rational_graph_value G rho) js"
      by (rule nth_equalityI) (use lengths Suc.IH[OF children] in auto)
    show ?thesis by (simp add: Fun root lists)
  qed
qed

text \<open>One finite observation can establish disequality of closed rational
values. Different graph node numbers alone never establish disequality.\<close>
fun lp_rational_distinct where
  "lp_rational_distinct 0 G i j = False"
| "lp_rational_distinct (Suc fuel) G i j =
    (i<length G \<and> j<length G \<and> (case (G!i,G!j) of
      (LPRBranch f xs,LPRBranch g ys) \<Rightarrow>
        f\<noteq>g \<or> length xs\<noteq>length ys \<or>
          list_ex (\<lambda>k. lp_rational_distinct fuel G (xs!k) (ys!k)) [0..<min (length xs) (length ys)]
      | _ \<Rightarrow> False))"

lemma lp_rational_distinct_sound:
  assumes "lp_rational_distinct fuel G i j"
  shows "lp_rational_graph_value G rho i\<noteq>lp_rational_graph_value G rho j"
  using assms
proof (induction fuel arbitrary: i j)
  case 0 then show ?case by simp
next
  case (Suc fuel)
  obtain f xs g ys where left: "G!i=LPRBranch f xs" and right: "G!j=LPRBranch g ys"
    and indices: "i<length G" "j<length G"
    and different: "f\<noteq>g \<or> length xs\<noteq>length ys \<or>
      (\<exists>k<min (length xs) (length ys). lp_rational_distinct fuel G (xs!k) (ys!k))"
    using Suc.prems by (auto simp: list_ex_iff split: lp_rational_node.splits; metis min.idem)
  have a: "lp_rational_graph_value G rho i=LPIFun f (map (lp_rational_graph_value G rho) xs)"
    by (rule lp_rational_graph_branch[OF lp_rational_graph_value_model indices(1) left])
  have b: "lp_rational_graph_value G rho j=LPIFun g (map (lp_rational_graph_value G rho) ys)"
    by (rule lp_rational_graph_branch[OF lp_rational_graph_value_model indices(2) right])
  show ?case using different Suc.IH
    by (auto simp: a b; metis length_map nth_map)
qed

lemma lp_rational_distinct_same_node_rejected:
  "\<not>lp_rational_distinct fuel G i i"
  using lp_rational_distinct_sound by blast

ML \<open>
val checked = [@{thm lp_rational_match_sound}, @{thm lp_rational_distinct_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted rational matching dependency" else ();
\<close>
end
