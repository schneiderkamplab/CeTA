theory LP_Cut_Return_Attachment
  imports LP_Cut_Return_Sequence LP_Cut_Allocate
begin

text \<open>Attach the suspended continuation using each choice frame's own
environment. In particular, backtracking does not apply the failed branch's
substitution to a saved alternative. These definitions do not erase cut scopes.
They are a source connection, not yet an accepting Split certificate rule.\<close>

fun lpc_attach_frame where
  "lpc_attach_frame rest (LPCGoals gs,\<eta>) =
    LPCGoals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest)"
| "lpc_attach_frame rest (LPCClause gs c m,\<eta>) =
    LPCClause (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest) c m"
| "lpc_attach_frame rest (LPCBarrier m,\<eta>) = LPCBarrier m"

abbreviation lpc_attach where
  "lpc_attach rest ss \<equiv> map (lpc_attach_frame rest) ss"

fun lpc_prefix_active where
  "lpc_prefix_active [] = False"
| "lpc_prefix_active ((LPCGoals gs,\<eta>)#ss) = (gs\<noteq>[])"
| "lpc_prefix_active ((LPCClause gs c m,\<eta>)#ss) = (gs\<noteq>[])"
| "lpc_prefix_active ((LPCBarrier m,\<eta>)#ss) = True"

lemma lpc_attach_prune:
  "lpc_attach rest (lpc_answer_prune m ss) = lp_cut_prune m (lpc_attach rest ss)"
  by (induct ss) (auto split: prod.splits lp_cut_entry.splits)

lemma lpc_attach_frame_scopes:
  "lp_cut_entry_scopes (fst frame) \<subseteq> lp_cut_entry_scopes (lpc_attach_frame rest frame)"
  by (cases frame; cases "fst frame") auto

lemma lpc_attach_fresh:
  "lp_cut_fresh m (lpc_attach rest ss) \<Longrightarrow> lp_cut_fresh m (map fst ss)"
  using lpc_attach_frame_scopes[of _ rest]
  by (auto simp: lp_cut_fresh_def; blast)

lemma lpc_attach_substituted_rest:
  "map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>))
    (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest) =
    map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>x. lp_isubst (\<eta> x) \<sigma>))) rest"
  by (simp add: map_map o_def lp_cut_map_comp lp_ieval_subst)

lemma lpc_attach_nonempty_head:
  "xs\<noteq>[] \<Longrightarrow> xs@ys=z#zs \<Longrightarrow>
    \<exists>tail. xs=z#tail \<and> zs=tail@ys"
  by (cases xs) auto

lemma lpc_attach_admin_reflect:
  assumes active: "lpc_prefix_active ss"
    and step: "lp_cut_admin (lpc_attach rest ss) = Some u"
  shows "\<exists>tt. lpc_answer_transition P ss None tt \<and> u=lpc_attach rest tt"
proof (cases ss)
  case Nil then show ?thesis using active by simp
next
  case (Cons frame es)
  obtain e \<eta> where frame: "frame=(e,\<eta>)" by (cases frame) auto
  show ?thesis
  proof (cases e)
    case (LPCBarrier m)
    then show ?thesis using step Cons frame
      by (auto intro: lpc_answer_transition.barrier)
  next
    case (LPCClause gs c m)
    then show ?thesis using step Cons frame by simp
  next
    case (LPCGoals gs)
    obtain g tail where gs: "gs=g#tail" using active Cons frame LPCGoals by (cases gs) auto
    show ?thesis
    proof (cases g)
      case (LPCCut m)
      have event: "lpc_answer_transition P ss None
        ((LPCGoals tail,\<eta>)#lpc_answer_prune m es)"
        using Cons frame LPCGoals gs LPCCut by (simp add: lpc_answer_transition.cut)
      show ?thesis using event step Cons frame LPCGoals gs LPCCut
        by (auto simp: lpc_attach_prune)
    qed (use active step Cons frame LPCGoals gs in
      \<open>auto intro: lpc_answer_transition.truth lpc_answer_transition.failure\<close>)
  qed
qed

text \<open>While the prefix is active, every concrete source step projects to
an annotated prefix step and commutes with attachment. Source-side MGU checks
include the suspended continuation; their safe projection was proved separately.
The successful-empty-prefix case is intentionally excluded: that is where the
continuation starts, and must not be confused with source backtracking.\<close>

theorem lpc_attach_active_reflect:
  fixes P :: "('f,string) lp_cut_program"
  assumes active: "lpc_prefix_active ss"
    and step: "(lpc_attach rest ss,u)\<in>lp_cut_mgu_source P"
  shows "\<exists>tt. lpc_answer_transition P ss None tt \<and> u=lpc_attach rest tt"
proof -
  obtain e \<eta> es where ss: "ss=(e,\<eta>)#es"
    using active by (cases ss; auto split: prod.splits)
  from step show ?thesis
  proof cases
    case admin
    show ?thesis by (rule lpc_attach_admin_reflect[OF active admin])
  next
    case (case_call m f ts gs tail)
    obtain prefix where shape: "e=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest"
      and tail: "tail=lpc_attach rest es"
      using case_call active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have fresh: "lp_cut_fresh m (map fst ss)"
      by (rule lpc_attach_fresh[where rest=rest]) (use case_call in simp)
    have event: "lpc_answer_transition P ss None
      (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#prefix) c m,\<eta>))
        (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,\<eta>)#es)"
      using fresh by (simp add: ss shape lpc_answer_transition.case_call)
    show ?thesis by (rule exI, rule conjI[OF event])
      (use case_call gs tail in \<open>simp add: map_map o_def\<close>)
  next
    case (resolve c a gs \<sigma> \<rho> m tail)
    obtain prefix where shape: "e=LPCClause (LPCAtom a#prefix) c m"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest"
      and tail: "tail=lpc_attach rest es"
      using resolve active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have mgu: "lpc_mgu_resolve a prefix (fst (P!c)) (snd (P!c)) \<sigma> \<rho>"
      by (rule lpc_mgu_resolve_prefix_projection)
        (use resolve gs in simp)
    have event: "lpc_answer_transition P ss None
      ((LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) prefix),
        \<lambda>x. lp_isubst (\<eta> x) \<sigma>)#es)"
      unfolding ss shape by (rule lpc_answer_transition.resolve) (use resolve mgu in auto)
    show ?thesis by (rule exI, rule conjI[OF event])
      (use resolve gs tail in \<open>simp add: map_map o_def lp_cut_map_comp lp_ieval_subst append_assoc\<close>)
  next
    case (backtrack c a gs m)
    obtain prefix where shape: "e=LPCClause (LPCAtom a#prefix) c m"
      and tail: "u=lpc_attach rest es"
      using backtrack active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have event: "lpc_answer_transition P ss None es"
      unfolding ss shape by (rule lpc_answer_transition.backtrack) (use backtrack in auto)
    show ?thesis by (rule exI, rule conjI[OF event]) (use backtrack tail in simp)
  next
    case (unify a b gs \<sigma> tail)
    obtain prefix where shape: "e=LPCGoals (LPCUnify a b#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest"
      and tail: "tail=lpc_attach rest es"
      using unify active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have mgu: "lpc_mgu_unify a b prefix \<sigma>"
      by (rule lpc_mgu_unify_prefix_projection) (use unify gs in simp)
    have event: "lpc_answer_transition P ss None
      ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) prefix),
        \<lambda>x. lp_isubst (\<eta> x) \<sigma>)#es)"
      unfolding ss shape by (rule lpc_answer_transition.unify[OF mgu])
    show ?thesis by (rule exI, rule conjI[OF event])
      (use unify gs tail in \<open>simp add: map_map o_def lp_cut_map_comp lp_ieval_subst\<close>)
  next
    case (unify_fail a b gs)
    obtain prefix where shape: "e=LPCGoals (LPCUnify a b#prefix)"
      and tail: "u=lpc_attach rest es"
      using unify_fail active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have event: "lpc_answer_transition P ss None es"
      unfolding ss shape by (rule lpc_answer_transition.unify_fail) (use unify_fail in auto)
    show ?thesis by (rule exI, rule conjI[OF event]) (use unify_fail tail in simp)
  next
    case (meta m a gs tail body)
    obtain prefix where shape: "e=LPCGoals (LPCMeta a#prefix)"
      and gs: "gs = prefix @ map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) rest"
      and tail: "tail=lpc_attach rest es"
      using meta active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have fresh: "lp_cut_fresh m (map fst ss)"
      by (rule lpc_attach_fresh[where rest=rest]) (use meta in simp)
    have event: "lpc_answer_transition P ss None
      ((LPCGoals (body@prefix),\<eta>)#(LPCBarrier m,\<eta>)#es)"
      using fresh meta by (auto simp: ss shape intro: lpc_answer_transition.meta)
    show ?thesis by (rule exI, rule conjI[OF event]) (use meta gs tail in \<open>simp add: append_assoc\<close>)
  next
    case (meta_unlowerable a gs tail)
    obtain prefix where shape: "e=LPCGoals (LPCMeta a#prefix)"
      using meta_unlowerable active ss by (cases e; auto dest: lpc_attach_nonempty_head)
    have event: "lpc_answer_transition P ss None ss"
      unfolding ss shape by (rule lpc_answer_transition.meta_unlowerable)
        (use meta_unlowerable in auto)
    show ?thesis by (rule exI, rule conjI[OF event]) (use meta_unlowerable in simp)
  qed
qed

end
