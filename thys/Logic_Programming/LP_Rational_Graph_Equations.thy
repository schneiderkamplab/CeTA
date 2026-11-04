theory LP_Rational_Graph_Equations
  imports LP_Ground_Equations
begin

text \<open>Finite graph descriptions denote existing infinitary runtime terms.
External nodes retain their valuation; branch references are checked against
the complete graph. Neither this relation nor uniqueness supplies finiteness.\<close>

datatype ('f,'v) lp_rational_node =
    lpr_is_external: LPRExternal (lpr_external: 'v)
  | lpr_is_branch: LPRBranch (lpr_label: 'f) (lpr_children: "nat list")

definition lp_rational_graph_valid where
  "lp_rational_graph_valid G =
    (\<forall>node\<in>set G. case node of LPRExternal x \<Rightarrow> True
      | LPRBranch f children \<Rightarrow> set children \<subseteq> {..<length G})"

definition lp_rational_graph_model where
  "lp_rational_graph_model G rho eta =
    (\<forall>i<length G. eta i = (case G!i of LPRExternal x \<Rightarrow> rho x
      | LPRBranch f children \<Rightarrow> LPIFun f (map eta children)))"

primcorec lp_rational_graph_value ::
  "('f,'v) lp_rational_node list \<Rightarrow> ('v \<Rightarrow> ('f,'w) lp_iterm) \<Rightarrow>
    nat \<Rightarrow> ('f,'w) lp_iterm" where
  "lp_rational_graph_value G rho i = (if lpr_is_external (G!i) then rho (lpr_external (G!i))
    else LPIFun (lpr_label (G!i)) (map (lp_rational_graph_value G rho) (lpr_children (G!i))))"

lemma lp_rational_graph_value_model:
  "lp_rational_graph_model G rho (lp_rational_graph_value G rho)"
  unfolding lp_rational_graph_model_def
  by (intro allI impI, subst lp_rational_graph_value.code)
    (auto split: lp_rational_node.splits)

lemma lp_rational_graph_external:
  "lp_rational_graph_model G rho eta \<Longrightarrow> i<length G \<Longrightarrow>
    G!i=LPRExternal x \<Longrightarrow> eta i=rho x"
  by (auto simp: lp_rational_graph_model_def)

lemma lp_rational_graph_branch:
  "lp_rational_graph_model G rho eta \<Longrightarrow> i<length G \<Longrightarrow>
    G!i=LPRBranch f children \<Longrightarrow> eta i=LPIFun f (map eta children)"
  by (auto simp: lp_rational_graph_model_def)

lemma lp_rational_graph_model_unique:
  assumes valid: "lp_rational_graph_valid G"
    and left: "lp_rational_graph_model G rho eta"
    and right: "lp_rational_graph_model G rho theta"
    and index: "i<length G"
  shows "eta i=theta i"
  using index
  by (coinduction arbitrary: i rule: lp_iterm.coinduct_strong)
    (use valid left right in
      \<open>auto simp: lp_rational_graph_valid_def lp_rational_graph_model_def
        list_all2_conv_all_nth split: lp_rational_node.splits;
        metis nth_mem lessThan_iff subsetD\<close>)


lemma lp_rational_graph_model_subst:
  assumes "lp_rational_graph_model G rho eta"
  shows "lp_rational_graph_model G (\<lambda>x. lp_isubst (rho x) sigma)
    (\<lambda>i. lp_isubst (eta i) sigma)"
  using assms
  by (auto simp: lp_rational_graph_model_def map_map
      split: lp_rational_node.splits)

lemma lp_rational_graph_value_subst:
  assumes "lp_rational_graph_valid G" "i<length G"
  shows "lp_isubst (lp_rational_graph_value G rho i) sigma =
    lp_rational_graph_value G (\<lambda>x. lp_isubst (rho x) sigma) i"
  by (rule lp_rational_graph_model_unique[OF assms(1)
        lp_rational_graph_model_subst[OF lp_rational_graph_value_model]
        lp_rational_graph_value_model assms(2)])

lemma lp_rational_graph_dangling_reference_rejected:
  "\<not>lp_rational_graph_valid [LPRBranch f [1]]"
  by (simp add: lp_rational_graph_valid_def)

lemma lp_rational_graph_self_cycle_not_finite:
  "\<not>lp_seg_ground (lp_rational_graph_value [LPRBranch f [0]] rho 0)"
proof -
  have nonfinite: "lp_seg_ground t \<Longrightarrow> t\<noteq>LPIFun f [t]" for t
    by (induction rule: lp_seg_ground.induct)
      (auto simp: list_all_iff; metis list.set_intros(1))
  have cycle: "lp_rational_graph_value [LPRBranch f [0]] rho 0 =
    LPIFun f [lp_rational_graph_value [LPRBranch f [0]] rho 0]"
    by (subst lp_rational_graph_value.code) simp
  show ?thesis using nonfinite cycle by blast
qed

fun lp_rational_node_term :: "('f,'v) lp_rational_node \<Rightarrow> ('f,nat+'v) term" where
  "lp_rational_node_term (LPRExternal x) = Var (Inr x)"
| "lp_rational_node_term (LPRBranch f children) = Fun f (map (\<lambda>i. Var (Inl i)) children)"

definition lp_rational_graph_equations where
  "lp_rational_graph_equations G =
    map (\<lambda>i. (Var (Inl i),lp_rational_node_term (G!i))) [0..<length G]"

lemma lp_rational_node_term_eval:
  "lp_ieval (lp_rational_node_term n) eta =
    (case n of LPRExternal x \<Rightarrow> eta (Inr x)
     | LPRBranch f children \<Rightarrow> LPIFun f (map (\<lambda>i. eta (Inl i)) children))"
  by (cases n) (simp_all add: map_map)

lemma lp_rational_graph_equations_model:
  "lp_equations (lp_rational_graph_equations G) eta \<longleftrightarrow>
    lp_rational_graph_model G (\<lambda>x. eta (Inr x)) (\<lambda>i. eta (Inl i))"
  by (auto simp: lp_equations_def lp_rational_graph_equations_def list_all_iff
      lp_rational_graph_model_def lp_rational_node_term_eval map_map split: lp_rational_node.splits)

lemma lp_rational_graph_equations_denote:
  assumes "lp_rational_graph_valid G" "lp_equations (lp_rational_graph_equations G) eta"
    "i<length G"
  shows "eta (Inl i)=lp_rational_graph_value G (\<lambda>x. eta (Inr x)) i"
  by (rule lp_rational_graph_model_unique[OF assms(1)
        iffD1[OF lp_rational_graph_equations_model assms(2)]
        lp_rational_graph_value_model assms(3)])

ML \<open>
val checked = [@{thm lp_rational_graph_model_unique}, @{thm lp_rational_graph_value_subst},
  @{thm lp_rational_graph_self_cycle_not_finite}, @{thm lp_rational_graph_equations_denote}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted rational graph equation dependency" else ();
\<close>
end
