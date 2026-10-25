theory LP_Cut_SEG_Connection_Check
  imports LP_Cut_SEG_Root_Representation
begin

record 'f lpc_seg_connection =
  lpcse_target :: nat
  lpcse_bindings :: "(string * 'f lpc_term) list"
  lpcse_swaps :: "(nat * nat) list"
  lpcse_continuation :: "'f lp_cut_symbol"
  lpcse_captured :: "'f lpc_term list"
  lpcse_ground_program :: "('f lp_cut_symbol,string) lp_clause list"
  lpcse_predicates :: "'f list"
  lpcse_modes :: "'f lp_cut_symbol lp_ground_mode list"

definition lpc_seg_named_template where
  "lpc_seg_named_template vs t = t\<cdot>
    (\<lambda>i. if i<length vs then Var (vs!i) else Fun LPCTruth [])"

definition lpc_seg_check_connection where
  "lpc_seg_check_connection P roots is_cont c d C R nd ss l outp receipt =
    (lpcse_target receipt<length roots \<and>
     (case ss of [(LPCGoals pre,observed)] \<Rightarrow>
       (let child_root=roots!lpcse_target receipt; child_nd=lpcsr_node child_root;
            vs=lpcn_vars nd; child_vs=lpcn_vars child_nd;
            mu=lp_cut_instance_subst (lpcse_bindings receipt);
            inp=lpcsr_input child_root\<cdot>mu;
            out=lpc_seg_named_template child_vs (lpcsr_output child_root)\<cdot>mu;
            final=lpc_seg_compose_observation observed outp;
            u=lpcse_continuation receipt; caps=lpcse_captured receipt in
        (case lpcn_state child_nd of [child] \<Rightarrow>
          lpc_seg_check_instance_boundary (LPCGoals pre) (lpcn_ground nd) (lpcn_guards nd) vs observed
            child (lpcn_ground child_nd) (lpcn_guards child_nd) child_vs (lpcse_bindings receipt) (lpcse_swaps receipt) \<and>
          is_cont u \<and>
          lpc_seg_check_encoded_pair 1 2 is_cont c d C R l (Fun u (inp#caps)) \<and>
          lpc_seg_check_encoded_pair 2 1 is_cont c d C R (Fun u (out#caps)) final \<and>
          vars_term out \<subseteq> set vs \<and> vars_term final \<subseteq> set vs \<and>
          lpc_seg_check_return_ground P pre (lpcn_ground nd) vs out
            (lpcse_ground_program receipt) (lpcse_predicates receipt) (lpcse_modes receipt) \<and>
          lpc_seg_compose_observation (map (lpc_seg_position_template vs) (map mu child_vs))
            (lpcsr_output child_root) = lpc_seg_position_template vs out \<and>
          lpc_seg_compose_observation (map (lpc_seg_position_template vs) observed) outp =
            lpc_seg_position_template vs final
          | _ \<Rightarrow> False))
       | _ \<Rightarrow> False))"

theorem lpc_seg_connection_checked_lower:
  assumes checked: "lpc_seg_check_connection P roots is_cont c d C R nd ss l outp receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and lower: "\<And>vs v out. (A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>,v)\<in>(qrstep False Q R)\<^sup>+ \<Longrightarrow>
      lpc_seg_root_rep roots is_cont c d vs v out \<Longrightarrow>
      lpc_return_contract P vs (qrstep False Q R) v out"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "lpc_return_contract P (lpc_return_eval eta ss) (qrstep False Q R)
    (A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d outp rho\<rangle>)"
proof -
  let ?i = "lpcse_target receipt"
  let ?root = "roots!?i"
  let ?nd = "lpcsr_node ?root"
  let ?vs = "lpcn_vars nd"
  let ?cvs = "lpcn_vars ?nd"
  let ?mu = "lp_cut_instance_subst (lpcse_bindings receipt)"
  let ?eta = "\<lambda>x. lp_ieval (?mu x) eta"
  let ?inp = "lpcsr_input ?root\<cdot>?mu"
  let ?out = "lpc_seg_named_template ?cvs (lpcsr_output ?root)\<cdot>?mu"
  let ?u = "lpcse_continuation receipt"
  let ?caps = "lpcse_captured receipt"
  let ?D = "More (c ?u) [] \<box>
    (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) ?caps)"
  have index: "?i<length roots" using checked by (simp add: lpc_seg_check_connection_def)
  have single: "length ss=1"
  proof (cases ss)
    case Nil then show ?thesis using checked by (simp add: lpc_seg_check_connection_def)
  next
    case (Cons p ps)
    obtain e observed where p: "p=(e,observed)" by (cases p) simp
    show ?thesis using checked Cons p
      by (cases ps; cases e) (simp_all add: lpc_seg_check_connection_def)
  qed
  obtain e observed where one: "ss=[(e,observed)]"
    using single by (cases ss) auto
  obtain pre where e: "e=LPCGoals pre"
    using checked by (cases e) (auto simp: lpc_seg_check_connection_def one)
  have ss: "ss=[(LPCGoals pre,observed)]" by (simp only: one e)
  have child_single: "length (lpcn_state ?nd)=1"
  proof (cases "lpcn_state ?nd")
    case Nil then show ?thesis using checked by (simp add: lpc_seg_check_connection_def ss Let_def)
  next
    case (Cons x xs)
    show ?thesis using checked Cons by (cases xs) (simp_all add: lpc_seg_check_connection_def ss Let_def)
  qed
  obtain child where child_state: "lpcn_state ?nd=[child]"
    using child_single by (cases "lpcn_state ?nd") auto
  have inst: "lpc_seg_check_instance_boundary (LPCGoals pre) (lpcn_ground nd) (lpcn_guards nd) ?vs observed
    child (lpcn_ground ?nd) (lpcn_guards ?nd) ?cvs (lpcse_bindings receipt) (lpcse_swaps receipt)"
    and cont: "is_cont ?u"
    and enter: "lpc_seg_check_encoded_pair 1 2 is_cont c d C R l (Fun ?u (?inp#?caps))"
    and leave: "lpc_seg_check_encoded_pair 2 1 is_cont c d C R (Fun ?u (?out#?caps)) (lpc_seg_compose_observation observed outp)"
    using checked by (auto simp: lpc_seg_check_connection_def ss child_state Let_def)
  have child_known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    by (rule lpc_seg_instance_boundary_knowledge[OF inst known])
  have call: "lp_seg_ground (lp_ieval ?inp eta) \<and>
    list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) ?caps \<and>
    (lpc_seg_return_value is_cont c d l eta,?D\<langle>lpc_seg_return_value is_cont c d ?inp eta\<rangle>)\<in>qrstep False Q R"
    using lpc_seg_checked_call[where Q=Q, OF enter cont finite range roots]
    by (simp only: lpc_seg_return_value_def)
  have child_finite: "lp_seg_ground (lp_ieval (lpcsr_input ?root) ?eta)"
    using call by (simp add: lp_ieval_finite_subst)
  have strict: "(A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>,
    (A\<circ>\<^sub>c ?D)\<langle>lpc_seg_return_value is_cont c d (lpcsr_input ?root) ?eta\<rangle>)\<in>(qrstep False Q R)\<^sup>+"
  proof -
    have step: "(A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>,
      A\<langle>?D\<langle>lpc_seg_return_value is_cont c d ?inp eta\<rangle>\<rangle>)\<in>qrstep False Q R"
      by (rule qrstep.ctxt) (use call in blast)
    show ?thesis using r_into_trancl[OF step]
      by (simp add: lpc_seg_return_value_def lp_ieval_finite_subst)
  qed
  have child_contract: "lpc_return_contract P (lpc_return_eval ?eta [(child,map Var ?cvs)]) (qrstep False Q R)
    (A\<langle>?D\<langle>lpc_seg_return_value is_cont c d ?inp eta\<rangle>\<rangle>)
    (\<lambda>rho. A\<langle>?D\<langle>lpc_seg_return_value is_cont c d (lpcsr_output ?root) rho\<rangle>\<rangle>)"
    using lpc_seg_root_lower[OF lower index child_known child_finite strict]
    by (simp add: lpc_seg_root_state_def child_state lpc_seg_return_value_def lp_ieval_finite_subst)
  show ?thesis unfolding ss
    by (rule lpc_seg_connection_contract[OF inst program known enter leave cont finite _ _ _ _ _ refl child_contract range roots])
      (use checked in \<open>auto simp: lpc_seg_check_connection_def ss child_state Let_def\<close>)
qed

end
