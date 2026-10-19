theory Higher_Order_Delegation_Foundation
  imports "Higher_Order_Lex.Higher_Order_Lex_Schema"
begin

text \<open>Infrastructure for first-order delegation. These lemmas do not
add an accepting checker branch. In particular, a first-order termination
certificate alone does not discharge the known-call premise below: the
first-order projection and source-computability bridge are still required.\<close>

lemma ho_finite_SN_reducts:
  assumes sn: "Wellfounded.accp (\<lambda>u t. step t u) t"
    and branching: "\<And>x. finite {y. step x y}"
  shows "finite {u. step\<^sup>*\<^sup>* t u}"
  using sn
proof (induction t rule: accp.induct)
  case (accI t)
  have children: "finite (\<Union>x\<in>{x. step t x}. {u. step\<^sup>*\<^sup>* x u})"
    by (rule finite_UN_I[OF branching]) (use accI.IH in auto)
  have cover: "{u. step\<^sup>*\<^sup>* t u} \<subseteq>
      {t} \<union> (\<Union>x\<in>{x. step t x}. {u. step\<^sup>*\<^sup>* x u})"
    by (auto elim: converse_rtranclpE)
  show ?case by (rule finite_subset[OF cover]) (use children in simp)
qed

fun ho_finite_choice where
  "ho_finite_choice combine z [] = z"
| "ho_finite_choice combine z (x#xs) = combine x (ho_finite_choice combine z xs)"

lemma ho_finite_choice_projects:
  assumes left: "\<And>x y. step (combine x y) x"
    and right: "\<And>x y. step (combine x y) y"
    and member: "x\<in>set xs"
  shows "step\<^sup>+\<^sup>+ (ho_finite_choice combine z xs) x"
  using member
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "x=y")
    case True
    then show ?thesis using left[of y "ho_finite_choice combine z ys"]
      by (auto intro: tranclp.r_into_trancl)
  next
    case False
    have tail: "step\<^sup>+\<^sup>+ (ho_finite_choice combine z ys) x"
      by (rule Cons.IH) (use Cons.prems False in simp)
    show ?thesis using right[of y "ho_finite_choice combine z ys"] tail
      by (auto intro: tranclp_trans tranclp.r_into_trancl)
  qed
qed

context ho_source_accessible_reducibility
begin

text \<open>Known calls must be computable in the original source relation,
not merely terminating in an extracted first-order fragment. This explicit
premise prevents the unfinished delegation bridge from being bypassed.\<close>

theorem ordered_recursive_calls_with_known:
  assumes wf: "wf Q"
    and argument_step: "\<And>c xs ys T. ho_lookup S c=Some T \<Longrightarrow>
      list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs \<Longrightarrow>
      ho_arguments_step S V R B xs ys \<Longrightarrow> ((c,ys),(c,xs))\<in>Q"
    and arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    and bounds: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arity c\<le>length (ho_argument_types T)"
    and known: "\<And>c xs T. c\<in>K \<Longrightarrow> ho_lookup S c=Some T \<Longrightarrow>
      list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs \<Longrightarrow>
      source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
    and closed: "\<And>c xs T u. c\<notin>K \<Longrightarrow> ho_lookup S c=Some T \<Longrightarrow>
      list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs \<Longrightarrow>
      ho_root_step S V R B (ho_apply_terms (HConst c) xs) u \<Longrightarrow>
      (\<And>d ys U. ((d,ys),(c,xs))\<in>Q \<Longrightarrow>
        ho_lookup S d=Some U \<Longrightarrow>
        list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
        source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)) \<Longrightarrow>
      source_candidate (ho_drop_type (arity c) T) u"
    and symbol: "ho_lookup S c=Some T"
    and args: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
  shows "source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
proof (rule ordered_recursive_calls_computable[where arity=arity, OF wf argument_step arities bounds _ symbol args])
  fix d ys U u
  assume sy: "ho_lookup S d=Some U"
    and aa: "list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys"
    and root: "ho_root_step S V R B (ho_apply_terms (HConst d) ys) u"
    and ih: "\<And>e zs W. ((e,zs),(d,ys))\<in>Q \<Longrightarrow>
      ho_lookup S e=Some W \<Longrightarrow>
      list_all2 source_candidate (take (arity e) (ho_argument_types W)) zs \<Longrightarrow>
      source_candidate (ho_drop_type (arity e) W) (ho_apply_terms (HConst e) zs)"
  show "source_candidate (ho_drop_type (arity d) U) u"
  proof (cases "d\<in>K")
    case True
    have comp: "source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
      by (rule known[OF True sy aa])
    have step: "ho_step S V R B (ho_apply_terms (HConst d) ys) u"
      using root unfolding ho_root_step_def by (blast intro: ho_step.rule)
    show ?thesis by (rule source_candidate_reduction[OF comp step])
  next
    case False
    show ?thesis by (rule closed[OF False sy aa root ih])
  qed
qed

end

end
