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

end
