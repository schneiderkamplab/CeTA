theory LP_Cut_Residual
  imports LP_Cut_Interface LP_Cut_Barriers LP_SEG_Residual
begin

text \<open>Every instance edge consumes a residual resolution step. In
particular, a cycle of instances is not accepted merely because the finite
graph is closed. The residual termination certificate must discharge it.\<close>

definition lp_cut_residual_edge where
  "lp_cut_residual_edge Q F V i j bindings =
    (((F i,map Var (V i)),
      [(F j,map (lp_cut_instance_subst bindings) (V j))]) \<in> set Q)"

lemma lp_cut_residual_edge_step:
  assumes "lp_cut_residual_edge Q F V i j bindings"
  shows "([(F i,map \<eta> (V i))],
    [(F j,map (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>) (V j))])
    \<in> lp_ild Q"
  using lp_seg_residual_step[of "(F i,map Var (V i))"
    "[(F j,map (lp_cut_instance_subst bindings) (V j))]" Q
    "(F i,map \<eta> (V i))" LPIVar \<eta> "[]"] assms
  by (simp add: lp_cut_residual_edge_def lp_atom_eval_def lp_iatom_subst_def o_def)

theorem lp_cut_recursive_residual_termination:
  assumes local: "\<And>i \<eta>.
      i \<in> I \<Longrightarrow> lp_cut_knowledge (set (G i)) (K i) \<eta> \<Longrightarrow>
      (\<And>j \<nu>. j \<in> I \<Longrightarrow>
        lp_cut_knowledge (set (G j)) (K j) \<nu> \<Longrightarrow>
        ([(F i,map \<eta> (V i))],[(F j,map \<nu> (V j))]) \<in> lp_ild Q \<Longrightarrow>
        SN_on (lp_cut_source P) {lp_cut_state_eval (N j) \<nu>}) \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
    and sn: "SN_on (lp_ild Q) {qs}"
    and root: "i \<in> I" "lp_cut_knowledge (set (G i)) (K i) \<eta>"
      "qs = [(F i,map \<eta> (V i))]"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
proof -
  have all: "\<forall>i \<eta>. i \<in> I \<longrightarrow>
      lp_cut_knowledge (set (G i)) (K i) \<eta> \<longrightarrow>
      qs = [(F i,map \<eta> (V i))] \<longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix xs
    assume ih: "\<And>ys. (xs,ys) \<in> lp_ild Q \<Longrightarrow>
      \<forall>j \<nu>. j \<in> I \<longrightarrow>
        lp_cut_knowledge (set (G j)) (K j) \<nu> \<longrightarrow>
        ys = [(F j,map \<nu> (V j))] \<longrightarrow>
        SN_on (lp_cut_source P) {lp_cut_state_eval (N j) \<nu>}"
    show "\<forall>i \<eta>. i \<in> I \<longrightarrow>
      lp_cut_knowledge (set (G i)) (K i) \<eta> \<longrightarrow>
      xs = [(F i,map \<eta> (V i))] \<longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
    proof (intro allI impI)
      fix i \<eta>
      assume member: "i \<in> I"
        and known: "lp_cut_knowledge (set (G i)) (K i) \<eta>"
        and xs: "xs = [(F i,map \<eta> (V i))]"
      show "SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
      proof (rule local[OF member known])
        fix j \<nu>
        assume j: "j \<in> I"
          and known_j: "lp_cut_knowledge (set (G j)) (K j) \<nu>"
          and edge: "([(F i,map \<eta> (V i))],[(F j,map \<nu> (V j))]) \<in> lp_ild Q"
        have step: "(xs,[(F j,map \<nu> (V j))]) \<in> lp_ild Q"
          using edge by (simp only: xs)
        show "SN_on (lp_cut_source P) {lp_cut_state_eval (N j) \<nu>}"
          using ih[OF step] j known_j by blast
      qed
    qed
  qed
  show ?thesis using all root by blast
qed

lemma lp_cut_instance_node_sound:
  assumes program: "lp_cut_source_program P"
    and checked: "lp_cut_check_instance (N i) (G i) (K i)
      (N j) (G j) (K j) bindings swaps"
    and edge: "lp_cut_residual_edge Q F V i j bindings"
    and knowledge: "lp_cut_knowledge (set (G i)) (K i) \<eta>"
    and ih: "\<And>\<nu>. lp_cut_knowledge (set (G j)) (K j) \<nu> \<Longrightarrow>
      ([(F i,map \<eta> (V i))],[(F j,map \<nu> (V j))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (N j) \<nu>}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
  by (rule lp_cut_checked_instance_SN[OF program checked];
    rule ih[OF lp_cut_checked_instance_knowledge[OF checked knowledge]
      lp_cut_residual_edge_step[OF edge]])

lemma lp_cut_admin_node_sound:
  assumes program: "lp_cut_source_program P"
    and admin: "lp_cut_check_admin (N i) next"
    and checked: "lp_cut_check_instance next (G i) (K i)
      (N j) (G j) (K j) bindings swaps"
    and edge: "lp_cut_residual_edge Q F V i j bindings"
    and knowledge: "lp_cut_knowledge (set (G i)) (K i) \<eta>"
    and ih: "\<And>\<nu>. lp_cut_knowledge (set (G j)) (K j) \<nu> \<Longrightarrow>
      ([(F i,map \<eta> (V i))],[(F j,map \<nu> (V j))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (N j) \<nu>}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
proof -
  have child: "SN_on (lp_cut_source P) {lp_cut_state_eval next \<eta>}"
    by (rule lp_cut_checked_instance_SN[OF program checked];
      rule ih[OF lp_cut_checked_instance_knowledge[OF checked knowledge]
        lp_cut_residual_edge_step[OF edge]])
  show ?thesis
  proof (rule step_reflects_SN_on)
    fix t assume step: "(lp_cut_state_eval (N i) \<eta>,t) \<in> lp_cut_source P"
    have "t=lp_cut_state_eval next \<eta>"
      using lp_cut_checked_admin_covers[OF admin step] by blast
    then show "SN_on (lp_cut_source P) {t}" using child by simp
  qed
qed

lemma lp_cut_terminal_node_sound:
  "SN_on (lp_cut_source P) {[]}"
  by (rule step_reflects_SN_on) (auto elim: lp_cut_source.cases)

lemma lp_cut_barrier_entry_map:
  "lp_cut_is_barrier (lp_cut_entry_map f e) = lp_cut_is_barrier e"
  by (cases e) simp_all

lemma lp_cut_barriers_state_map:
  "lp_cut_barriers (lp_cut_state_map f bs) = lp_cut_barriers bs"
  by (induct bs) (simp_all add: lp_cut_state_map_def lp_cut_barrier_entry_map)

lemma lp_cut_trim_node_sound:
  assumes program: "lp_cut_source_program P"
    and shape: "N i=next@bs" "lp_cut_barriers bs"
    and checked: "lp_cut_check_instance next (G i) (K i)
      (N j) (G j) (K j) bindings swaps"
    and edge: "lp_cut_residual_edge Q F V i j bindings"
    and knowledge: "lp_cut_knowledge (set (G i)) (K i) \<eta>"
    and ih: "\<And>\<nu>. lp_cut_knowledge (set (G j)) (K j) \<nu> \<Longrightarrow>
      ([(F i,map \<eta> (V i))],[(F j,map \<nu> (V j))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (N j) \<nu>}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
proof -
  have child: "SN_on (lp_cut_source P) {lp_cut_state_eval next \<eta>}"
    by (rule lp_cut_checked_instance_SN[OF program checked];
      rule ih[OF lp_cut_checked_instance_knowledge[OF checked knowledge]
        lp_cut_residual_edge_step[OF edge]])
  have barriers: "lp_cut_barriers (lp_cut_state_eval bs \<eta>)"
    using shape(2) by (simp only: lp_cut_barriers_state_map)
  show ?thesis using lp_cut_append_barriers_SN[OF child barriers] shape(1)
    by (simp add: lp_cut_state_map_def)
qed

lemma lp_cut_allocated_node_sound:
  assumes program: "lp_cut_source_program P"
    and covers: "\<And>t. (lp_cut_state_eval (N i) \<eta>,t) \<in> lp_cut_source P \<Longrightarrow>
      \<exists>m n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) (lp_cut_state_eval next \<eta>)"
    and checked: "lp_cut_check_instance next (G i) (K i)
      (N j) (G j) (K j) bindings swaps"
    and edge: "lp_cut_residual_edge Q F V i j bindings"
    and knowledge: "lp_cut_knowledge (set (G i)) (K i) \<eta>"
    and ih: "\<And>\<nu>. lp_cut_knowledge (set (G j)) (K j) \<nu> \<Longrightarrow>
      ([(F i,map \<eta> (V i))],[(F j,map \<nu> (V j))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (N j) \<nu>}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
proof -
  have child: "SN_on (lp_cut_source P) {lp_cut_state_eval next \<eta>}"
    by (rule lp_cut_checked_instance_SN[OF program checked];
      rule ih[OF lp_cut_checked_instance_knowledge[OF checked knowledge]
        lp_cut_residual_edge_step[OF edge]])
  show ?thesis
  proof (rule step_reflects_SN_on)
    fix t assume step: "(lp_cut_state_eval (N i) \<eta>,t) \<in> lp_cut_source P"
    obtain m n where t: "t=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
      (lp_cut_state_eval next \<eta>)" using covers[OF step] by blast
    show "SN_on (lp_cut_source P) {t}"
      using lp_cut_scope_swap_preserves_SN[OF program child, of m n] by (simp only: t)
  qed
qed

lemma lp_cut_normalized_residual_step:
  assumes clause: "((f,inputs),[(g,outputs)]) \<in> set Q"
    and equations: "lp_equations eqs \<eta>'"
    and normalized: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) vs) =
      Some (Some (map LPCAtom inputs))"
    and old: "map \<eta>' vs=map \<eta> vs"
  shows "([(f,map \<eta> vs)],[(g,map (\<lambda>t. lp_ieval t \<eta>') outputs)]) \<in> lp_ild Q"
proof -
  have matched: "map (\<lambda>t. lp_ieval t \<eta>') inputs=map \<eta> vs"
    using lp_cut_normalized_terms[OF equations, of fuel "map Var vs" inputs] normalized old
    by (simp add: map_map o_def)
  show ?thesis
    using lp_seg_residual_step[OF clause, where a="(f,map \<eta> vs)"
      and \<sigma>=LPIVar and \<rho>="\<eta>'" and rest="[]"] matched
    by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def)
qed

end
