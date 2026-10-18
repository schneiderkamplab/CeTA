theory Relative_ADP_Com_Reduction_Pair
  imports
    Relative_ADP_Derelatification_Dev.Relative_ADP_Derelatification
    Ord.Reduction_Pair
    "HOL-Combinatorics.List_Permutation"
begin

datatype 'f adp_com_symbol =
    ADP_Symbol "'f adp_symbol"
  | Com0
  | Com2

lemma map_funs_plain_adp_term:
  "map_funs_term ADP_Symbol (plain_adp_term t) =
    map_funs_term (ADP_Symbol \<circ> adp_symbol.Plain) t"
  by (induction t) simp_all

fun adp_combine_terms ::
  "('f adp_com_symbol, 'v) term list \<Rightarrow>
   ('f adp_com_symbol, 'v) term" where
  "adp_combine_terms [] = Fun Com0 []"
| "adp_combine_terms [t] = t"
| "adp_combine_terms (t # u # ts) =
    Fun Com2 [t, adp_combine_terms (u # ts)]"

definition relative_adp_term_annotation_components ::
  "('f adp_symbol, 'v) term \<Rightarrow>
   ('f adp_com_symbol, 'v) term list" where
  "relative_adp_term_annotation_components t = map
    (\<lambda>p. map_funs_term ADP_Symbol (mark_adp_root (t |_ p)))
    (sorted_list_of_set (sharp_positions t))"

definition relative_adp_term_annotation_summary ::
  "('f adp_symbol, 'v) term \<Rightarrow>
   ('f adp_com_symbol, 'v) term" where
  "relative_adp_term_annotation_summary t = adp_combine_terms
    (relative_adp_term_annotation_components t)"

lemma finite_relative_adp_sharp_positions:
  "finite (sharp_positions t)"
  unfolding sharp_positions_def
  by (rule finite_subset[OF _ finite_poss]) auto

lemma relative_adp_term_annotation_components_set:
  "set (relative_adp_term_annotation_components t) =
    (\<lambda>p. map_funs_term ADP_Symbol (mark_adp_root (t |_ p))) `
      sharp_positions t"
  unfolding relative_adp_term_annotation_components_def
  by (simp add: finite_relative_adp_sharp_positions)

lemma relative_adp_term_annotation_summary_unmarked:
  assumes "sharp_positions t = {}"
  shows "relative_adp_term_annotation_summary t = Fun Com0 []"
  using assms unfolding relative_adp_term_annotation_summary_def
    relative_adp_term_annotation_components_def by simp

definition relative_adp_annotation_summary ::
  "('f, 'v) adp \<Rightarrow> ('f adp_com_symbol, 'v) term" where
  "relative_adp_annotation_summary pair = adp_combine_terms
    (map (map_funs_term ADP_Symbol \<circ> mark_adp_root)
      (annotated_rhs_subterms_list pair))"

definition adp_com_monotone ::
  "(('f adp_com_symbol, 'v) term \<times>
     ('f adp_com_symbol, 'v) term) set \<Rightarrow> bool" where
  "adp_com_monotone S \<longleftrightarrow> (\<forall>s1 s2 t.
    (s1,s2) \<in> S \<longrightarrow>
      (Fun Com2 [s1,t], Fun Com2 [s2,t]) \<in> S \<and>
      (Fun Com2 [t,s1], Fun Com2 [t,s2]) \<in> S)"

text \<open>Only compound contexts need strict monotonicity. Ordinary
symbols retain the weak context closure of a reduction triple.\<close>

locale adp_com_redtriple_order = redtriple_order S NS NST
  for S :: "(('f adp_com_symbol, 'v) term \<times> ('f adp_com_symbol, 'v) term) set"
    and NS NST +
  assumes com_mono: "adp_com_monotone S"

definition adp_com_invariant ::
  "(('f adp_com_symbol, 'v) term \<times>
     ('f adp_com_symbol, 'v) term) set \<Rightarrow> bool" where
  "adp_com_invariant NS \<longleftrightarrow> (\<forall>x y z.
    (Fun Com2 [x,y], Fun Com2 [y,x]) \<in> NS \<and>
    (Fun Com2 [y,x], Fun Com2 [x,y]) \<in> NS \<and>
    (Fun Com2 [x, Fun Com2 [y,z]],
      Fun Com2 [Fun Com2 [x,y],z]) \<in> NS \<and>
    (Fun Com2 [Fun Com2 [x,y],z],
      Fun Com2 [x, Fun Com2 [y,z]]) \<in> NS)"

definition adp_com_discarding ::
  "(('f adp_com_symbol, 'v) term \<times>
     ('f adp_com_symbol, 'v) term) set \<Rightarrow> bool" where
  "adp_com_discarding NS \<longleftrightarrow> (\<forall>x y.
    (Fun Com2 [x,y], x) \<in> NS \<and>
    (Fun Com2 [x,y], y) \<in> NS \<and>
    (x, Fun Com0 []) \<in> NS)"

text \<open>
  The published proof of the relative ADP reduction-pair processor drops
  annotations that are not transported by the VRF.  Commutativity,
  associativity, and strict Com-monotonicity alone do not justify that step.
  The explicit discarding laws above state the property used by the proof.
  They hold for the intended natural interpretation Com0 = 0 and
  Com2(x,y) = x + y.
\<close>

lemma adp_combine_terms_list_all2:
  assumes refl: "refl NS"
    and trans: "trans NS"
    and ctxt: "ctxt.closed NS"
    and related: "list_all2 (\<lambda>s t. (s,t) \<in> NS) xs ys"
  shows "(adp_combine_terms xs, adp_combine_terms ys) \<in> NS"
  using related
proof (induction xs arbitrary: ys)
  case Nil
  then have "ys = []" by simp
  then show ?case using refl unfolding refl_on_def by simp
next
  case (Cons x xs)
  then obtain y ys' where ys: "ys = y # ys'"
    and head_rel: "(x,y) \<in> NS"
    and tail_rel: "list_all2 (\<lambda>s t. (s,t) \<in> NS) xs ys'"
    by (cases ys) auto
  show ?case
  proof (cases xs)
    case Nil
    then have "ys' = []" using tail_rel by simp
    with Nil ys head_rel show ?thesis by simp
  next
    case (Cons x' xs')
    then obtain y' ys'' where ys': "ys' = y' # ys''"
      using tail_rel by (cases ys') auto
    have head: "(Fun Com2 [x, adp_combine_terms xs],
        Fun Com2 [y, adp_combine_terms xs]) \<in> NS"
      using ctxt_closed_one[OF ctxt head_rel,
        of Com2 "[]" "[adp_combine_terms xs]"] by simp
    have tail: "(adp_combine_terms xs, adp_combine_terms ys') \<in> NS"
      by (rule Cons.IH[OF tail_rel])
    have tail_context: "(Fun Com2 [y, adp_combine_terms xs],
        Fun Com2 [y, adp_combine_terms ys']) \<in> NS"
      using ctxt_closed_one[OF ctxt tail,
        of Com2 "[y]" "[]"] by simp
    have combined: "(Fun Com2 [x, adp_combine_terms xs],
        Fun Com2 [y, adp_combine_terms ys']) \<in> NS"
      using trans head tail_context unfolding trans_def by blast
    show ?thesis using combined unfolding Cons ys ys' by simp
  qed
qed

lemma adp_combine_terms_delete:
  assumes ctxt: "ctxt.closed NS"
    and discard: "adp_com_discarding NS"
  shows "(adp_combine_terms (xs @ x # ys),
      adp_combine_terms (xs @ ys)) \<in> NS"
proof (induction xs)
  case Nil
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using discard
      unfolding adp_com_discarding_def by simp
  next
    case (Cons y ys')
    then show ?thesis using discard
      unfolding adp_com_discarding_def by simp
  qed
next
  case (Cons a xs)
  show ?case
  proof (cases "xs @ ys")
    case Nil
    then have xs: "xs = []" and ys: "ys = []" by auto
    then show ?thesis using discard
      unfolding adp_com_discarding_def by simp
  next
    case (Cons z zs)
    have tail: "(adp_combine_terms (xs @ x # ys),
        adp_combine_terms (xs @ ys)) \<in> NS"
      by (rule Cons.IH)
    have lifted: "(Fun Com2 [a, adp_combine_terms (xs @ x # ys)],
        Fun Com2 [a, adp_combine_terms (xs @ ys)]) \<in> NS"
      using ctxt_closed_one[OF ctxt tail, of Com2 "[a]" "[]"] by simp
    show ?thesis
      using lifted Cons by (cases xs) simp_all
  qed
qed

lemma adp_combine_terms_swap_adjacent:
  assumes trans: "trans NS"
    and ctxt: "ctxt.closed NS"
    and invariant: "adp_com_invariant NS"
  shows "(adp_combine_terms (xs @ a # b # ys),
      adp_combine_terms (xs @ b # a # ys)) \<in> NS"
proof (induction xs)
  case Nil
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using invariant
      unfolding adp_com_invariant_def by simp
  next
    case (Cons z zs)
    let ?tail = "adp_combine_terms (z # zs)"
    have assoc1: "(Fun Com2 [a, Fun Com2 [b,?tail]],
        Fun Com2 [Fun Com2 [a,b],?tail]) \<in> NS"
      using invariant unfolding adp_com_invariant_def by blast
    have comm: "(Fun Com2 [a,b], Fun Com2 [b,a]) \<in> NS"
      using invariant unfolding adp_com_invariant_def by blast
    have comm_context: "(Fun Com2 [Fun Com2 [a,b],?tail],
        Fun Com2 [Fun Com2 [b,a],?tail]) \<in> NS"
      using ctxt_closed_one[OF ctxt comm, of Com2 "[]" "[?tail]"]
      by simp
    have assoc2: "(Fun Com2 [Fun Com2 [b,a],?tail],
        Fun Com2 [b, Fun Com2 [a,?tail]]) \<in> NS"
      using invariant unfolding adp_com_invariant_def by blast
    have first_two: "(Fun Com2 [a, Fun Com2 [b,?tail]],
        Fun Com2 [Fun Com2 [b,a],?tail]) \<in> NS"
      using trans assoc1 comm_context unfolding trans_def by blast
    have all: "(Fun Com2 [a, Fun Com2 [b,?tail]],
        Fun Com2 [b, Fun Com2 [a,?tail]]) \<in> NS"
      using trans first_two assoc2 unfolding trans_def by blast
    show ?thesis using all unfolding Cons by simp
  qed
next
  case (Cons x xs)
  have tail: "(adp_combine_terms (xs @ a # b # ys),
      adp_combine_terms (xs @ b # a # ys)) \<in> NS"
    by (rule Cons.IH)
  have lifted: "(Fun Com2 [x, adp_combine_terms (xs @ a # b # ys)],
      Fun Com2 [x, adp_combine_terms (xs @ b # a # ys)]) \<in> NS"
    using ctxt_closed_one[OF ctxt tail, of Com2 "[x]" "[]"] by simp
  show ?case using lifted by (cases xs) simp_all
qed

lemma adp_combine_terms_cons_nonempty:
  assumes "xs \<noteq> []"
  shows "adp_combine_terms (x # xs) =
    Fun Com2 [x, adp_combine_terms xs]"
  using assms by (cases xs) simp_all

lemma adp_combine_terms_move_right:
  assumes refl: "refl NS"
    and trans: "trans NS"
    and ctxt: "ctxt.closed NS"
    and invariant: "adp_com_invariant NS"
  shows "(adp_combine_terms (x # (xs @ ys)),
      adp_combine_terms (xs @ (x # ys))) \<in> NS"
proof (induction xs)
  case Nil
  then show ?case using refl unfolding refl_on_def by simp
next
  case (Cons a xs)
  have swap: "(adp_combine_terms (x # a # (xs @ ys)),
      adp_combine_terms (a # x # (xs @ ys))) \<in> NS"
    using adp_combine_terms_swap_adjacent[
      OF trans ctxt invariant, where xs="[]" and a=x and b=a
        and ys="xs @ ys"] by simp
  have tail: "(adp_combine_terms (x # (xs @ ys)),
      adp_combine_terms (xs @ (x # ys))) \<in> NS"
    by (rule Cons.IH)
  have lifted: "(adp_combine_terms (a # x # (xs @ ys)),
      adp_combine_terms (a # (xs @ (x # ys)))) \<in> NS"
    using ctxt_closed_one[OF ctxt tail, of Com2 "[a]" "[]"]
    by (simp add: adp_combine_terms_cons_nonempty)
  show ?case
    using transD[OF trans, OF swap lifted] by simp
qed

lemma adp_combine_terms_permutation:
  assumes refl: "refl NS"
    and trans: "trans NS"
    and ctxt: "ctxt.closed NS"
    and invariant: "adp_com_invariant NS"
    and permutation: "mset xs = mset ys"
  shows "(adp_combine_terms xs, adp_combine_terms ys) \<in> NS"
  using permutation
proof (induction xs arbitrary: ys)
  case Nil
  then have "ys = []" by simp
  then show ?case using refl unfolding refl_on_def by simp
next
  case (Cons x xs)
  have ys_mset: "mset ys = add_mset x (mset xs)"
    using Cons.prems by simp
  have "x \<in># mset ys" unfolding ys_mset by simp
  then have x_in: "x \<in> set ys" by simp
  then obtain before after where ys: "ys = before @ (x # after)"
    by (meson split_list)
  have tails: "mset xs = mset (before @ after)"
    using Cons.prems unfolding ys by simp
  have tail: "(adp_combine_terms xs,
      adp_combine_terms (before @ after)) \<in> NS"
    by (rule Cons.IH[OF tails])
  have heads: "(adp_combine_terms (x # xs),
      adp_combine_terms (x # (before @ after))) \<in> NS"
  proof (cases xs)
    case Nil
    then have "before @ after = []" using tails by simp
    with Nil show ?thesis using refl unfolding refl_on_def by simp
  next
    case (Cons a as)
    then have "before @ after \<noteq> []" using tails by auto
    then obtain b bs where ba: "before @ after = b # bs"
      by (cases "before @ after") auto
    have "(Fun Com2 [x, adp_combine_terms xs],
        Fun Com2 [x, adp_combine_terms (before @ after)]) \<in> NS"
      using ctxt_closed_one[OF ctxt tail, of Com2 "[x]" "[]"] by simp
    then show ?thesis unfolding Cons ba by simp
  qed
  have moved: "(adp_combine_terms (x # (before @ after)),
      adp_combine_terms (before @ (x # after))) \<in> NS"
    by (rule adp_combine_terms_move_right[
          OF refl trans ctxt invariant])
  show ?case unfolding ys
    using trans heads moved unfolding trans_def by blast
qed

lemma adp_combine_terms_append_pack:
  assumes refl: "refl NS"
    and trans: "trans NS"
    and ctxt: "ctxt.closed NS"
    and invariant: "adp_com_invariant NS"
    and xs: "xs \<noteq> []"
    and ys: "ys \<noteq> []"
  shows "(Fun Com2 [adp_combine_terms xs, adp_combine_terms ys],
      adp_combine_terms (xs @ ys)) \<in> NS"
  using xs
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases xs)
    case Nil
    with ys show ?thesis
      using refl unfolding refl_on_def
      by (simp add: adp_combine_terms_cons_nonempty)
  next
    case (Cons a as)
    have assoc: "(Fun Com2 [Fun Com2 [x, adp_combine_terms xs],
          adp_combine_terms ys],
        Fun Com2 [x, Fun Com2 [adp_combine_terms xs,
          adp_combine_terms ys]]) \<in> NS"
      using invariant unfolding adp_com_invariant_def by blast
    have packed_tail: "(Fun Com2 [adp_combine_terms xs,
          adp_combine_terms ys],
        adp_combine_terms (xs @ ys)) \<in> NS"
      by (rule Cons.IH) (use Cons in simp)
    have lifted: "(Fun Com2 [x, Fun Com2 [adp_combine_terms xs,
          adp_combine_terms ys]],
        Fun Com2 [x, adp_combine_terms (xs @ ys)]) \<in> NS"
      using ctxt_closed_one[OF ctxt packed_tail, of Com2 "[x]" "[]"]
      by simp
    have combined: "(Fun Com2 [Fun Com2 [x, adp_combine_terms xs],
          adp_combine_terms ys],
        Fun Com2 [x, adp_combine_terms (xs @ ys)]) \<in> NS"
      using trans assoc lifted unfolding trans_def by blast
    show ?thesis using combined Cons ys
      by (simp add: adp_combine_terms_cons_nonempty)
  qed
qed

lemma adp_combine_terms_prepend_summary:
  assumes refl: "refl NS"
    and trans: "trans NS"
    and ctxt: "ctxt.closed NS"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
  shows "(adp_combine_terms (adp_combine_terms xs # ys),
      adp_combine_terms (xs @ ys)) \<in> NS"
proof (cases xs)
  case Nil
  show ?thesis
  proof (cases ys)
    case Nil
    with `xs = []` show ?thesis using refl unfolding refl_on_def by simp
  next
    case (Cons y ys')
    with Nil show ?thesis using discard
      unfolding adp_com_discarding_def
      by (simp add: adp_combine_terms_cons_nonempty)
  qed
next
  case (Cons x xs')
  have xs_nonempty: "xs \<noteq> []" using Cons by simp
  show ?thesis
  proof (cases ys)
    case Nil
    with Cons show ?thesis using refl unfolding refl_on_def by simp
  next
    case (Cons y ys')
    have packed: "(Fun Com2 [adp_combine_terms xs,
          adp_combine_terms ys], adp_combine_terms (xs @ ys)) \<in> NS"
      by (rule adp_combine_terms_append_pack[
          OF refl trans ctxt invariant])
         (use xs_nonempty `ys = y # ys'` in simp_all)
    show ?thesis using packed Cons `ys = y # ys'`
      by (simp add: adp_combine_terms_cons_nonempty)
  qed
qed

lemma adp_combine_terms_replace_head_strict:
  assumes strict_mono: "adp_com_monotone S"
    and ns_refl: "refl NS"
    and ns_trans: "trans NS"
    and ns_ctxt: "ctxt.closed NS"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and compat: "S O NS \<subseteq> S"
    and head: "(x, adp_combine_terms generated) \<in> S"
    and tails: "list_all2 (\<lambda>s t. (s,t) \<in> NS) source target"
  shows "(adp_combine_terms (x # source),
      adp_combine_terms (generated @ target)) \<in> S"
proof (cases source)
  case Nil
  then have target: "target = []" using tails by simp
  show ?thesis
  proof (cases generated)
    case Nil
    with `source = []` target show ?thesis using head by simp
  next
    case (Cons f fs)
    with `source = []` target show ?thesis using head by simp
  qed
next
  case (Cons s ss)
  then obtain t ts where target: "target = t # ts"
    using tails by (cases target) auto
  have tail_rel: "(adp_combine_terms source,
      adp_combine_terms target) \<in> NS"
    by (rule adp_combine_terms_list_all2[
          OF ns_refl ns_trans ns_ctxt tails])
  have strict_head: "(Fun Com2 [x, adp_combine_terms source],
      Fun Com2 [adp_combine_terms generated,
        adp_combine_terms source]) \<in> S"
    using strict_mono head unfolding adp_com_monotone_def by blast
  have weak_tail: "(Fun Com2 [adp_combine_terms generated,
        adp_combine_terms source],
      Fun Com2 [adp_combine_terms generated,
        adp_combine_terms target]) \<in> NS"
    using ctxt_closed_one[OF ns_ctxt tail_rel,
      of Com2 "[adp_combine_terms generated]" "[]"] by simp
  have packed: "(adp_combine_terms
        (adp_combine_terms generated # target),
      adp_combine_terms (generated @ target)) \<in> NS"
    by (rule adp_combine_terms_prepend_summary[
          OF ns_refl ns_trans ns_ctxt invariant discard])
  have weak: "(Fun Com2 [adp_combine_terms generated,
        adp_combine_terms source],
      adp_combine_terms (generated @ target)) \<in> NS"
  proof -
    have packed': "(Fun Com2 [adp_combine_terms generated,
          adp_combine_terms target],
        adp_combine_terms (generated @ target)) \<in> NS"
      using packed target
      by (simp add: adp_combine_terms_cons_nonempty)
    show ?thesis
      using ns_trans weak_tail packed' unfolding trans_def by blast
  qed
  have strict: "(Fun Com2 [x, adp_combine_terms source],
      adp_combine_terms (generated @ target)) \<in> S"
    using compat strict_head weak unfolding relcomp_def by blast
  show ?thesis using strict Cons
    by (simp add: adp_combine_terms_cons_nonempty)
qed

lemma relative_adp_annotation_summary_empty:
  assumes "annotated_rhs_subterms_list pair = []"
  shows "relative_adp_annotation_summary pair = Fun Com0 []"
  using assms unfolding relative_adp_annotation_summary_def by simp

lemma relative_adp_annotation_summary_singleton:
  assumes "annotated_rhs_subterms_list pair = [t]"
  shows "relative_adp_annotation_summary pair =
    map_funs_term ADP_Symbol (mark_adp_root t)"
  using assms unfolding relative_adp_annotation_summary_def by simp

lemma relative_adp_annotation_summary_pair:
  assumes "annotated_rhs_subterms_list pair = [s,t]"
  shows "relative_adp_annotation_summary pair =
    Fun Com2 [map_funs_term ADP_Symbol (mark_adp_root s),
      map_funs_term ADP_Symbol (mark_adp_root t)]"
  using assms unfolding relative_adp_annotation_summary_def by simp

definition relative_adp_fresh_positions ::
  "bool \<Rightarrow> ('f, 'v) adp \<Rightarrow> pos \<Rightarrow> pos set" where
  "relative_adp_fresh_positions at_sharp pair redex =
    (if at_sharp then (\<lambda>q. redex @ q) ` sharp_positions (snd pair)
     else {})"

lemma relative_adp_fresh_position_is_sharp:
  assumes applied:
      "relative_adp_applied_at P at_sharp s t pair redex"
    and fresh: "q' \<in> relative_adp_fresh_positions at_sharp pair redex"
  shows "q' \<in> sharp_positions t"
proof -
  have at: at_sharp using fresh
    unfolding relative_adp_fresh_positions_def by (cases at_sharp) auto
  from fresh at have image:
      "q' \<in> (\<lambda>alpha. redex @ alpha) ` sharp_positions (snd pair)"
    unfolding relative_adp_fresh_positions_def by simp
  then obtain alpha where
      alpha: "alpha \<in> sharp_positions (snd pair)"
    and q': "q' = redex @ alpha" by blast
  from applied obtain l r phi sigma A where pair: "pair = (l,r)"
    and edge_data:
      "(l,r) \<in> P" "plain_adp_term_pred l" "valid_vrf (l,r) phi"
      "redex \<in> fun_poss s" "at_sharp = (redex \<in> sharp_positions s)"
      "erase_adp_term (s |_ redex) = erase_adp_term l \<cdot> sigma"
      "A = (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ redex)"
      "t = replace_at s redex
        (annotate_term A (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_applied_at_def by blast
  have source: "redex \<in> sharp_positions s" using edge_data(5) at by simp
  have origin: "relative_adp_canonical_origin_edge P at_sharp s t pair
      redex redex q'"
  proof -
    have alpha_r: "alpha \<in> sharp_positions r" using alpha pair by simp
    show ?thesis
      unfolding relative_adp_canonical_origin_edge_def
      apply (intro exI conjI)
      using pair edge_data at alpha_r q'
      by (auto intro: origin_edge.root_target)
  qed
  show ?thesis
    by (rule relative_adp_canonical_origin_edge_preserves_sharp[
          OF origin source])
qed

lemma relative_adp_nonfresh_has_nonredex_predecessor:
  assumes applied:
      "relative_adp_applied_at P at_sharp s t pair redex"
    and lhs_fun: "is_Fun (fst pair)"
    and target: "q' \<in> sharp_positions t"
    and nonfresh:
      "q' \<notin> relative_adp_fresh_positions at_sharp pair redex"
  obtains q where
    "q \<in> sharp_positions s"
    "q \<noteq> redex"
    "relative_adp_canonical_origin_edge P at_sharp s t
      pair redex q q'"
proof -
  from relative_adp_applied_at_sharp_position_has_predecessor[
      OF applied target]
  obtain q where source: "q \<in> sharp_positions s"
    and origin: "relative_adp_canonical_origin_edge P at_sharp s t
      pair redex q q'" .
  have nonredex: "q \<noteq> redex"
  proof
    assume q: "q = redex"
    from applied obtain l r phi sigma A where pair: "pair = (l,r)"
      unfolding relative_adp_applied_at_def by blast
    have erased_lhs_fun: "is_Fun (erase_adp_term l)"
      using lhs_fun unfolding pair by (cases l) auto
    from origin obtain l' r' phi' sigma' A' where
      pair': "pair = (l',r')"
      and edge: "origin_edge (erase_adp_term l') (erase_adp_term r')
        redex sigma' (if at_sharp then sharp_positions r' else {})
        phi' q q'"
      unfolding relative_adp_canonical_origin_edge_def by blast
    have l': "l' = l" and r': "r' = r" using pair pair' by auto
    from origin_edge_from_redex_is_root_target[
        OF edge[unfolded q] erased_lhs_fun[unfolded l'[symmetric]]]
    obtain alpha where roots:
        "alpha \<in> (if at_sharp then sharp_positions r' else {})"
      and q': "q' = redex @ alpha" .
    have "q' \<in> relative_adp_fresh_positions at_sharp pair redex"
      using roots q' unfolding relative_adp_fresh_positions_def pair'
      by (cases at_sharp) auto
    with nonfresh show False by contradiction
  qed
  show thesis by (rule that[OF source nonredex origin])
qed

definition relative_adp_applied_with ::
  "('f, 'v) adp set \<Rightarrow> bool \<Rightarrow>
   ('f adp_symbol, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow>
   ('f, 'v) adp \<Rightarrow> pos \<Rightarrow> (pos \<Rightarrow> pos option) \<Rightarrow>
   ('v \<Rightarrow> ('f, 'v) term) \<Rightarrow> pos set \<Rightarrow> bool" where
  "relative_adp_applied_with P at_sharp s t pair redex phi sigma A \<longleftrightarrow>
    (case pair of (l,r) \<Rightarrow>
      (l,r) \<in> P \<and> plain_adp_term_pred l \<and> valid_vrf (l,r) phi \<and>
      redex \<in> fun_poss s \<and>
      at_sharp = (redex \<in> sharp_positions s) \<and>
      erase_adp_term (s |_ redex) = erase_adp_term l \<cdot> sigma \<and>
      A = (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ redex) \<and>
      t = replace_at s redex
        (annotate_term A (erase_adp_term r \<cdot> sigma)))"

lemma relative_adp_applied_with_imp_applied_at:
  assumes "relative_adp_applied_with P at_sharp s t pair redex phi sigma A"
  shows "relative_adp_applied_at P at_sharp s t pair redex"
  using assms unfolding relative_adp_applied_with_def
    relative_adp_applied_at_def by (cases pair) auto

definition relative_adp_fixed_nonredex_origin ::
  "('f, 'v) adp \<Rightarrow> bool \<Rightarrow> pos \<Rightarrow>
   (pos \<Rightarrow> pos option) \<Rightarrow> ('v \<Rightarrow> ('f, 'v) term) \<Rightarrow>
   pos \<Rightarrow> pos \<Rightarrow> bool" where
  "relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma q q' \<longleftrightarrow>
    q \<noteq> redex \<and> origin_edge (erase_adp_term (fst pair))
      (erase_adp_term (snd pair)) redex sigma
      (if at_sharp then sharp_positions (snd pair) else {}) phi q q'"

lemma relative_adp_fixed_nonredex_origin_functional:
  assumes first: "relative_adp_fixed_nonredex_origin pair at_sharp redex
      phi sigma q q1"
    and second: "relative_adp_fixed_nonredex_origin pair at_sharp redex
      phi sigma q q2"
  shows "q1 = q2"
  using assms unfolding relative_adp_fixed_nonredex_origin_def
  by (blast intro: origin_edge_nonroot_unique)

lemma relative_adp_fixed_nonfresh_covered:
  assumes applied:
      "relative_adp_applied_with P at_sharp s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
    and target: "q' \<in> sharp_positions t"
    and nonfresh:
      "q' \<notin> relative_adp_fresh_positions at_sharp pair redex"
  obtains q where "q \<in> sharp_positions s" "q \<noteq> redex"
    "relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma q q'"
proof -
  obtain l r where pair: "pair = (l,r)" by (cases pair)
  from applied have rule: "(l,r) \<in> P"
    and valid: "valid_vrf (l,r) phi"
    and redex_fun: "redex \<in> fun_poss s"
    and at: "at_sharp = (redex \<in> sharp_positions s)"
    and annotations: "A =
      (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ redex)"
    and target_term: "t = replace_at s redex
      (annotate_term A (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_applied_with_def pair by auto
  have redex_poss: "redex \<in> poss s"
    by (rule fun_poss_imp_poss[OF redex_fun])
  from pos_cases[of redex q']
  consider (below) "redex \<le>\<^sub>p q'"
    | (above) "q' <\<^sub>p redex"
    | (parallel) "redex \<bottom> q'" by blast
  then show thesis
  proof cases
    case below
    from prefixE[OF below] obtain alpha where q': "q' = redex @ alpha"
      by blast
    have redex_after: "redex \<in> poss t"
      unfolding target_term
      by (rule replace_at_below_poss[OF redex_poss]) simp
    have local_target: "alpha \<in> sharp_positions
        (annotate_term A (erase_adp_term r \<cdot> sigma))"
      using target sharp_positions_below_iff[OF redex_after, of alpha]
        replace_at_subt_at[OF redex_poss]
      unfolding target_term q' by simp
    from local_target have alpha_poss:
        "alpha \<in> poss (annotate_term A (erase_adp_term r \<cdot> sigma))"
      unfolding sharp_positions_def by auto
    have alpha_erased_poss: "alpha \<in> poss (erase_adp_term r \<cdot> sigma)"
      using alpha_poss poss_annotate_term_at[of A "[]"
        "erase_adp_term r \<cdot> sigma"]
      unfolding annotate_term_def by simp
    from local_target obtain f n where alpha_root:
        "root (annotate_term A (erase_adp_term r \<cdot> sigma) |_ alpha) =
          Some (f,n)"
      unfolding sharp_positions_def
      by (auto split: option.splits prod.splits)
    have alpha_fun: "alpha \<in> fun_poss (erase_adp_term r \<cdot> sigma)"
    proof (rule poss_is_Fun_fun_poss[OF alpha_erased_poss])
      show "is_Fun (erase_adp_term r \<cdot> sigma |_ alpha)"
        using alpha_root erase_annotate_term[of A "erase_adp_term r \<cdot> sigma"]
          erase_adp_term_subt_at[OF alpha_poss]
        by (cases "annotate_term A (erase_adp_term r \<cdot> sigma) |_ alpha")
           auto
    qed
    have alpha_A: "alpha \<in> A"
      using local_target sharp_positions_annotate_term[OF alpha_fun] by simp
    have not_root: "alpha \<notin>
        (if at_sharp then sharp_positions r else {})"
    proof
      assume root: "alpha \<in>
          (if at_sharp then sharp_positions r else {})"
      then have sharp: "at_sharp \<and> alpha \<in> sharp_positions r"
        by (cases at_sharp) auto
      then have "q' \<in> relative_adp_fresh_positions at_sharp pair redex"
        unfolding relative_adp_fresh_positions_def pair q' by auto
      with nonfresh show False by contradiction
    qed
    from alpha_A annotations not_root have transported:
        "alpha \<in> transported_annotations phi l (s |_ redex)" by auto
    then obtain rho alpha0 beta where alpha_eq: "alpha = alpha0 @ beta"
      and rho: "rho \<in> var_poss l" and phi0: "phi rho = Some alpha0"
      and source_local: "rho @ beta \<in> sharp_positions (s |_ redex)"
      unfolding transported_annotations_def by auto
    have source: "redex @ rho @ beta \<in> sharp_positions s"
      using source_local sharp_positions_below_iff[OF redex_poss,
        of "rho @ beta"] by simp
    have rho_erased: "rho \<in> var_poss (erase_adp_term l)"
      using rho var_poss_erase_adp_term by simp
    have alpha_fun': "alpha0 @ beta \<in> fun_poss (erase_adp_term r \<cdot> sigma)"
      using alpha_fun alpha_eq by simp
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
        redex sigma (if at_sharp then sharp_positions r else {}) phi
        (redex @ rho @ beta) q'"
      unfolding q' alpha_eq
      by (rule origin_edge.variable_transport[
            where rho=rho and l="erase_adp_term l" and phi=phi and
              alpha=alpha0 and beta=beta and r="erase_adp_term r" and
              sigma=sigma and p=redex and
              A="if at_sharp then sharp_positions r else {}"])
         (rule rho_erased, rule phi0, rule alpha_fun')
    have rho_nonempty: "rho \<noteq> []"
      using rho lhs_fun unfolding pair
      by (cases l) auto
    have nonredex: "redex @ rho @ beta \<noteq> redex"
      using rho_nonempty by auto
    show thesis
    proof (rule that[OF source nonredex])
      show "relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma
          (redex @ rho @ beta) q'"
        using edge nonredex unfolding relative_adp_fixed_nonredex_origin_def pair
        by (cases at_sharp) auto
    qed
  next
    case above
    have source: "q' \<in> sharp_positions s"
      using target sharp_positions_replace_outside_iff[OF redex_poss]
      unfolding target_term by (simp add: above)
    have nonredex: "q' \<noteq> redex" using above by auto
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
        redex sigma (if at_sharp then sharp_positions r else {}) phi q' q'"
      by (rule origin_edge.preserved) (rule disjI1[OF above])
    show thesis
    proof (rule that[OF source nonredex])
      show "relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma q' q'"
        using edge nonredex unfolding relative_adp_fixed_nonredex_origin_def pair
        by (cases at_sharp) auto
    qed
  next
    case parallel
    have outside: "q' \<bottom> redex" by (rule parallel_pos_sym[OF parallel])
    have source: "q' \<in> sharp_positions s"
      using target sharp_positions_replace_outside_iff[OF redex_poss]
      unfolding target_term by (simp add: outside)
    have nonredex: "q' \<noteq> redex" using parallel by auto
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
        redex sigma (if at_sharp then sharp_positions r else {}) phi q' q'"
      by (rule origin_edge.preserved) (rule disjI2[OF outside])
    show thesis
    proof (rule that[OF source nonredex])
      show "relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma q' q'"
        using edge nonredex unfolding relative_adp_fixed_nonredex_origin_def pair
        by (cases at_sharp) auto
    qed
  qed
qed

definition relative_adp_nonfresh_target_positions ::
  "bool \<Rightarrow> ('f, 'v) adp \<Rightarrow> pos \<Rightarrow>
   ('f adp_symbol, 'v) term \<Rightarrow> pos list" where
  "relative_adp_nonfresh_target_positions at_sharp pair redex t =
    filter (\<lambda>q. q \<notin>
      relative_adp_fresh_positions at_sharp pair redex)
      (sorted_list_of_set (sharp_positions t))"

definition relative_adp_nonfresh_predecessor ::
  "(pos \<Rightarrow> pos \<Rightarrow> bool) \<Rightarrow>
   ('f adp_symbol, 'v) term \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> pos" where
  "relative_adp_nonfresh_predecessor origin s redex q' =
    (SOME q. q \<in> sharp_positions s \<and> q \<noteq> redex \<and>
      origin q q')"

lemma relative_adp_nonfresh_predecessor_sound:
  assumes covered: "\<exists>q. q \<in> sharp_positions s \<and>
      q \<noteq> redex \<and> origin q q'"
  shows "relative_adp_nonfresh_predecessor origin s redex q'
      \<in> sharp_positions s"
    and "relative_adp_nonfresh_predecessor origin s redex q'
      \<noteq> redex"
    and "origin (relative_adp_nonfresh_predecessor origin s redex q') q'"
proof -
  have choice: "relative_adp_nonfresh_predecessor origin s redex q'
      \<in> sharp_positions s \<and>
      relative_adp_nonfresh_predecessor origin s redex q'
        \<noteq> redex \<and>
      origin (relative_adp_nonfresh_predecessor origin s redex q') q'"
    unfolding relative_adp_nonfresh_predecessor_def
    by (rule someI_ex) (use covered in blast)
  from choice show
      "relative_adp_nonfresh_predecessor origin s redex q'
        \<in> sharp_positions s"
    and "relative_adp_nonfresh_predecessor origin s redex q'
        \<noteq> redex"
    and "origin (relative_adp_nonfresh_predecessor origin s redex q') q'"
    by auto
qed

lemma relative_adp_nonfresh_predecessor_injective:
  assumes covered1: "\<exists>q. q \<in> sharp_positions s \<and>
      q \<noteq> redex \<and> origin q q1"
    and covered2: "\<exists>q. q \<in> sharp_positions s \<and>
      q \<noteq> redex \<and> origin q q2"
    and same: "relative_adp_nonfresh_predecessor origin s redex q1 =
      relative_adp_nonfresh_predecessor origin s redex q2"
    and origin_functional: "\<And>q a b.
      origin q a \<Longrightarrow> origin q b \<Longrightarrow> a = b"
  shows "q1 = q2"
proof -
  let ?source =
    "relative_adp_nonfresh_predecessor origin s redex q1"
  have edge1: "origin ?source q1"
    by (rule relative_adp_nonfresh_predecessor_sound(3)[
        where origin=origin and s=s and redex=redex and q'=q1,
        OF covered1])
  have edge2: "origin ?source q2"
    using relative_adp_nonfresh_predecessor_sound(3)[
      where origin=origin and s=s and redex=redex and q'=q2,
      OF covered2] same by simp
  show ?thesis by (rule origin_functional[OF edge1 edge2])
qed

lemma relative_adp_nonfresh_components_multiset_subset:
  assumes covered: "\<And>q'. q' \<in> set targets \<Longrightarrow>
      \<exists>q. q \<in> sharp_positions s \<and>
        q \<noteq> redex \<and> origin q q'"
    and origin_functional: "\<And>q a b.
      origin q a \<Longrightarrow> origin q b \<Longrightarrow> a = b"
    and distinct_targets: "distinct targets"
  shows "mset (map (relative_adp_nonfresh_predecessor origin s redex)
      targets) \<subseteq># mset
      (sorted_list_of_set (sharp_positions s - {redex}))"
proof -
  have pred_member: "relative_adp_nonfresh_predecessor origin s
      redex q \<in> sharp_positions s - {redex}"
    if "q \<in> set targets" for q
  proof -
    have witness: "\<exists>p. p \<in> sharp_positions s \<and>
        p \<noteq> redex \<and> origin p q" by (rule covered[OF that])
    have source: "relative_adp_nonfresh_predecessor origin s redex q
        \<in> sharp_positions s"
      by (rule relative_adp_nonfresh_predecessor_sound(1)[
          where origin=origin and s=s and redex=redex and q'=q, OF witness])
    have not_redex: "relative_adp_nonfresh_predecessor origin s redex q
        \<noteq> redex"
      by (rule relative_adp_nonfresh_predecessor_sound(2)[
          where origin=origin and s=s and redex=redex and q'=q, OF witness])
    show ?thesis using source not_redex by simp
  qed
  have inj_preds: "inj_on
      (relative_adp_nonfresh_predecessor origin s redex) (set targets)"
  proof (rule inj_onI)
    fix x y
    assume x: "x \<in> set targets"
      and y: "y \<in> set targets"
      and eq: "relative_adp_nonfresh_predecessor origin s redex x =
        relative_adp_nonfresh_predecessor origin s redex y"
    show "x = y"
      by (rule relative_adp_nonfresh_predecessor_injective[
          OF covered[OF x] covered[OF y] eq origin_functional])
  qed
  have distinct_preds: "distinct
      (map (relative_adp_nonfresh_predecessor origin s redex) targets)"
    using distinct_targets inj_preds by (simp add: distinct_map)
  have set_subset: "set (map
      (relative_adp_nonfresh_predecessor origin s redex) targets)
      \<subseteq> sharp_positions s - {redex}"
    using pred_member by auto
  have source_distinct:
      "distinct (sorted_list_of_set (sharp_positions s - {redex}))" by simp
  have source_set: "set (sorted_list_of_set (sharp_positions s - {redex})) =
      sharp_positions s - {redex}"
    using finite_relative_adp_sharp_positions[of s] by simp
  show ?thesis
    unfolding subseteq_mset_def
  proof
    fix x
    show "count (mset (map
          (relative_adp_nonfresh_predecessor origin s redex) targets)) x \<le>
        count (mset (sorted_list_of_set (sharp_positions s - {redex}))) x"
    proof (cases "x \<in> set (map
        (relative_adp_nonfresh_predecessor origin s redex) targets)")
      case False
      then have left_zero: "count (mset (map
          (relative_adp_nonfresh_predecessor origin s redex) targets)) x = 0"
        by (simp add: count_eq_zero_iff)
      then show ?thesis by simp
    next
      case True
      then have source_member:
          "x \<in> set (sorted_list_of_set (sharp_positions s - {redex}))"
        using set_subset source_set by blast
      have left_one: "count (mset (map
          (relative_adp_nonfresh_predecessor origin s redex) targets)) x = 1"
        using distinct_preds True by (simp add: distinct_count_atmost_1)
      have right_one: "count (mset
          (sorted_list_of_set (sharp_positions s - {redex}))) x = 1"
        using source_distinct source_member
        by (simp add: distinct_count_atmost_1)
      show ?thesis using left_one right_one by simp
    qed
  qed
qed

definition relative_adp_components_at ::
  "('f adp_symbol, 'v) term \<Rightarrow> pos list \<Rightarrow>
   ('f adp_com_symbol, 'v) term list" where
  "relative_adp_components_at t ps = map
    (\<lambda>p. map_funs_term ADP_Symbol (mark_adp_root (t |_ p))) ps"

definition relative_adp_fresh_target_positions_list ::
  "('f, 'v) adp \<Rightarrow> pos \<Rightarrow> pos list" where
  "relative_adp_fresh_target_positions_list pair redex = map
    ((@) redex) (sorted_list_of_set (sharp_positions (snd pair)))"

lemma distinct_relative_adp_poss_list:
  "distinct (poss_list t)"
proof (induct t)
  case (Fun f ts)
  let ?xss = "map (\<lambda>i. map ((#) i) (poss_list (ts ! i)))
    [0..<length ts]"
  have id: "map2 (\<lambda>i. map ((#) i)) [0..<length ts]
      (map poss_list ts) =
    ?xss"
    by (intro nth_equalityI) auto
  have outer_distinct: "distinct ?xss"
    unfolding distinct_map
  proof (intro conjI inj_onI)
    show "distinct [0..<length ts]" by simp
    fix i j
    assume i: "i \<in> set [0..<length ts]"
      and j: "j \<in> set [0..<length ts]"
      and equal: "map ((#) i) (poss_list (ts ! i)) =
        map ((#) j) (poss_list (ts ! j))"
    from equal show "i = j"
      by (cases "ts ! i"; cases "ts ! j")
        (simp_all add: poss_list.simps)
  qed
  have child_distinct: "\<And>ys. ys \<in> set ?xss \<Longrightarrow> distinct ys"
  proof -
    fix ys
    assume "ys \<in> set ?xss"
    then obtain i where i: "i < length ts"
      and ys: "ys = map ((#) i) (poss_list (ts ! i))" by auto
    show "distinct ys" unfolding ys distinct_map
      using Fun[of "ts ! i"] i by (auto simp: inj_on_def)
  qed
  have child_disjoint: "\<And>ys zs. ys \<in> set ?xss \<Longrightarrow>
      zs \<in> set ?xss \<Longrightarrow> ys \<noteq> zs \<Longrightarrow>
      set ys \<inter> set zs = {}"
  proof -
    fix ys zs
    assume ys_mem: "ys \<in> set ?xss"
      and zs_mem: "zs \<in> set ?xss"
      and different: "ys \<noteq> zs"
    then obtain i j where
      ys: "ys = map ((#) i) (poss_list (ts ! i))" and
      zs: "zs = map ((#) j) (poss_list (ts ! j))" and
      i: "i < length ts" and j: "j < length ts" by auto
    have "i \<noteq> j"
    proof
      assume "i = j"
      then have "ys = zs" using ys zs by simp
      then show False using different by contradiction
    qed
    then show "set ys \<inter> set zs = {}" unfolding ys zs by auto
  qed
  have concat_distinct: "distinct (concat ?xss)"
    by (rule distinct_concat[OF outer_distinct child_distinct child_disjoint])
  have root_fresh: "[] \<notin> set (concat ?xss)" by auto
  show ?case unfolding poss_list.simps id
    using root_fresh concat_distinct by simp
qed (simp add: poss_list.simps)

lemma relative_adp_components_at_mset_cong:
  assumes "mset ps = mset qs"
  shows "mset (relative_adp_components_at t ps) =
    mset (relative_adp_components_at t qs)"
proof -
  let ?f = "\<lambda>p. map_funs_term ADP_Symbol
    (mark_adp_root (t |_ p))"
  have "image_mset ?f (mset ps) = image_mset ?f (mset qs)"
    by (rule arg_cong[OF assms])
  then show ?thesis unfolding relative_adp_components_at_def by simp
qed

lemma relative_adp_fresh_target_positions_list_set:
  "set (relative_adp_fresh_target_positions_list pair redex) =
    relative_adp_fresh_positions True pair redex"
  unfolding relative_adp_fresh_target_positions_list_def
    relative_adp_fresh_positions_def
  using finite_relative_adp_sharp_positions[of "snd pair"] by simp

lemma relative_adp_target_position_partition:
  assumes applied: "relative_adp_applied_at P True s t pair redex"
  shows "mset (relative_adp_fresh_target_positions_list pair redex @
      relative_adp_nonfresh_target_positions True pair redex t) =
    mset (sorted_list_of_set (sharp_positions t))"
proof -
  let ?fresh = "relative_adp_fresh_target_positions_list pair redex"
  let ?nonfresh =
    "relative_adp_nonfresh_target_positions True pair redex t"
  have fresh_subset: "set ?fresh \<subseteq> sharp_positions t"
    using relative_adp_fresh_position_is_sharp[OF applied]
    unfolding relative_adp_fresh_target_positions_list_set by blast
  have fresh_distinct: "distinct ?fresh"
    unfolding relative_adp_fresh_target_positions_list_def
    by (simp add: distinct_map inj_on_def)
  have nonfresh_distinct: "distinct ?nonfresh"
    unfolding relative_adp_nonfresh_target_positions_def by simp
  have disjoint: "set ?fresh \<inter> set ?nonfresh = {}"
    unfolding relative_adp_nonfresh_target_positions_def
      relative_adp_fresh_target_positions_list_set by auto
  have nonfresh_set: "set ?nonfresh = sharp_positions t - set ?fresh"
  proof -
    have fresh_set: "set ?fresh =
        relative_adp_fresh_positions True pair redex"
      by (rule relative_adp_fresh_target_positions_list_set)
    show ?thesis
      unfolding relative_adp_nonfresh_target_positions_def
      using finite_relative_adp_sharp_positions[of t] fresh_set by auto
  qed
  have set_partition: "set (?fresh @ ?nonfresh) = sharp_positions t"
    using fresh_subset nonfresh_set by auto
  have distinct_partition: "distinct (?fresh @ ?nonfresh)"
    using fresh_distinct nonfresh_distinct disjoint by simp
  have distinct_target: "distinct (sorted_list_of_set (sharp_positions t))"
    by simp
  show ?thesis
  proof -
    have sets: "set (?fresh @ ?nonfresh) =
        set (sorted_list_of_set (sharp_positions t))"
      using set_partition finite_relative_adp_sharp_positions[of t] by simp
    show ?thesis
      using set_eq_iff_mset_eq_distinct[OF distinct_partition distinct_target]
        sets by blast
  qed
qed

lemma relative_adp_source_position_partition:
  assumes applied: "relative_adp_applied_at P True s t pair redex"
    and covered: "\<And>q'. q' \<in> set
      (relative_adp_nonfresh_target_positions True pair redex t) \<Longrightarrow>
      \<exists>q. q \<in> sharp_positions s \<and>
        q \<noteq> redex \<and> origin q q'"
    and origin_functional: "\<And>q a b.
      origin q a \<Longrightarrow> origin q b \<Longrightarrow> a = b"
  obtains leftovers where
    "mset (redex # map
        (relative_adp_nonfresh_predecessor origin s redex)
        (relative_adp_nonfresh_target_positions True pair redex t) @
        leftovers) =
      mset (sorted_list_of_set (sharp_positions s))"
proof -
  let ?targets =
    "relative_adp_nonfresh_target_positions True pair redex t"
  let ?pred = "map
    (relative_adp_nonfresh_predecessor origin s redex) ?targets"
  let ?source_rest =
    "sorted_list_of_set (sharp_positions s - {redex})"
  have distinct_targets: "distinct ?targets"
    unfolding relative_adp_nonfresh_target_positions_def
    by (rule distinct_filter, rule distinct_sorted_list_of_set)
  have pred_subset: "mset ?pred \<subseteq># mset ?source_rest"
    by (rule relative_adp_nonfresh_components_multiset_subset[
          OF covered origin_functional distinct_targets])
  from mset_le_perm_append[THEN iffD1, OF pred_subset]
  obtain leftovers where rest:
      "mset (?pred @ leftovers) = mset ?source_rest"
    by blast
  from applied have redex: "redex \<in> sharp_positions s"
    unfolding relative_adp_applied_at_def by blast
  have source: "mset (redex # ?source_rest) =
      mset (sorted_list_of_set (sharp_positions s))"
  proof -
    have d1: "distinct (redex # ?source_rest)"
      using redex finite_relative_adp_sharp_positions[of s] by simp
    have d2: "distinct (sorted_list_of_set (sharp_positions s))" by simp
    have sets: "set (redex # ?source_rest) =
        set (sorted_list_of_set (sharp_positions s))"
      using redex finite_relative_adp_sharp_positions[of s] by auto
    show ?thesis
      by (rule iffD1[OF set_eq_iff_mset_eq_distinct[OF d1 d2] sets])
  qed
  show thesis by (rule that[of leftovers]) (use rest source in simp)
qed

lemma relative_adp_component_step_lift:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and applied: "relative_adp_applied_at P True s t pair redex"
    and covered: "\<And>q'. q' \<in> set
      (relative_adp_nonfresh_target_positions True pair redex t) \<Longrightarrow>
      \<exists>q. q \<in> sharp_positions s \<and>
        q \<noteq> redex \<and> origin q q'"
    and origin_functional: "\<And>q a b.
      origin q a \<Longrightarrow> origin q b \<Longrightarrow> a = b"
    and root_strict:
      "(map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)),
        adp_combine_terms (relative_adp_components_at t
          (relative_adp_fresh_target_positions_list pair redex))) \<in> S"
    and transported_weak: "list_all2 (\<lambda>q q'.
      (map_funs_term ADP_Symbol (mark_adp_root (s |_
          relative_adp_nonfresh_predecessor origin s redex q')),
       map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
      (relative_adp_nonfresh_target_positions True pair redex t)
      (relative_adp_nonfresh_target_positions True pair redex t)"
  shows "(relative_adp_term_annotation_summary s,
      relative_adp_term_annotation_summary t) \<in> S"
proof -
  interpret adp_com_redtriple_order S NS NST by (rule order)
  have com_mono: "adp_com_monotone S"
    by (rule adp_com_redtriple_order.com_mono[OF order])
  let ?targets =
    "relative_adp_nonfresh_target_positions True pair redex t"
  let ?pred = "map
    (relative_adp_nonfresh_predecessor origin s redex) ?targets"
  let ?fresh = "relative_adp_fresh_target_positions_list pair redex"
  obtain leftovers where source_positions:
      "mset (redex # ?pred @ leftovers) =
        mset (sorted_list_of_set (sharp_positions s))"
    by (rule relative_adp_source_position_partition[
          OF applied covered origin_functional])
  have source_components: "mset
      (relative_adp_components_at s (redex # ?pred @ leftovers)) =
    mset (relative_adp_term_annotation_components s)"
  proof -
    have mapped: "mset
        (relative_adp_components_at s (redex # ?pred @ leftovers)) =
      mset (relative_adp_components_at s
        (sorted_list_of_set (sharp_positions s)))"
      by (rule relative_adp_components_at_mset_cong[OF source_positions])
    show ?thesis using mapped
      unfolding relative_adp_term_annotation_components_def
        relative_adp_components_at_def .
  qed
  have source_permute: "(relative_adp_term_annotation_summary s,
      adp_combine_terms
        (relative_adp_components_at s (redex # ?pred @ leftovers))) \<in> NS"
    unfolding relative_adp_term_annotation_summary_def
    by (rule adp_combine_terms_permutation[
        OF refl_NS trans_NS ctxt_NS invariant])
       (use source_components in simp)
  have target_positions:
      "mset (?fresh @ ?targets) =
        mset (sorted_list_of_set (sharp_positions t))"
    by (rule relative_adp_target_position_partition[OF applied])
  have target_components: "mset
      (relative_adp_components_at t (?fresh @ ?targets)) =
    mset (relative_adp_term_annotation_components t)"
  proof -
    have mapped: "mset
        (relative_adp_components_at t (?fresh @ ?targets)) =
      mset (relative_adp_components_at t
        (sorted_list_of_set (sharp_positions t)))"
      by (rule relative_adp_components_at_mset_cong[OF target_positions])
    show ?thesis using mapped
      unfolding relative_adp_term_annotation_components_def
        relative_adp_components_at_def .
  qed
  have target_permute: "(adp_combine_terms
      (relative_adp_components_at t (?fresh @ ?targets)),
      relative_adp_term_annotation_summary t) \<in> NS"
    unfolding relative_adp_term_annotation_summary_def
    by (rule adp_combine_terms_permutation[
        OF refl_NS trans_NS ctxt_NS invariant])
       (use target_components in simp)
  have tails: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
      (relative_adp_components_at s (?pred @ leftovers))
      (relative_adp_components_at t ?targets @
        map (\<lambda>p. Fun Com0 []) leftovers)"
  proof -
    have transported: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
        (relative_adp_components_at s ?pred)
        (relative_adp_components_at t ?targets)"
      using transported_weak
      unfolding relative_adp_components_at_def
      by (induction ?targets) auto
    have dropped: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
        (relative_adp_components_at s leftovers)
        (map (\<lambda>p. Fun Com0 []) leftovers)"
      using discard unfolding adp_com_discarding_def
        relative_adp_components_at_def by (induction leftovers) auto
    show ?thesis using list_all2_appendI[OF transported dropped]
      unfolding relative_adp_components_at_def by simp
  qed
  have strict_replaced: "(adp_combine_terms
        (relative_adp_components_at s (redex # ?pred @ leftovers)),
      adp_combine_terms
        (relative_adp_components_at t ?fresh @
          (relative_adp_components_at t ?targets @
            map (\<lambda>p. Fun Com0 []) leftovers))) \<in> S"
  proof -
    have strict0: "(adp_combine_terms
        (map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)) #
          relative_adp_components_at s (?pred @ leftovers)),
      adp_combine_terms
        (relative_adp_components_at t ?fresh @
          (relative_adp_components_at t ?targets @
            map (\<lambda>p. Fun Com0 []) leftovers))) \<in> S"
      by (rule adp_combine_terms_replace_head_strict[
          OF com_mono refl_NS trans_NS ctxt_NS invariant discard
            compat_S_NS root_strict tails])
    show ?thesis using strict0
      unfolding relative_adp_components_at_def by simp
  qed
  have dropped_target: "(adp_combine_terms
        (relative_adp_components_at t ?fresh @
          (relative_adp_components_at t ?targets @
            map (\<lambda>p. Fun Com0 []) leftovers)),
      adp_combine_terms
        (relative_adp_components_at t (?fresh @ ?targets))) \<in> NS"
  proof -
    have deletes: "(adp_combine_terms
        (relative_adp_components_at t (?fresh @ ?targets) @
          map (\<lambda>p. Fun Com0 []) leftovers),
      adp_combine_terms
        (relative_adp_components_at t (?fresh @ ?targets))) \<in> NS"
    proof (induction leftovers)
      case Nil
      then show ?case using refl_NS unfolding refl_on_def by simp
    next
      case (Cons p ps)
      note one = adp_combine_terms_delete[OF ctxt_NS discard,
        where xs="relative_adp_components_at t (?fresh @ ?targets)"
          and x="Fun Com0 []" and ys="map (\<lambda>p. Fun Com0 []) ps"]
      show ?case
        using trans_NS one Cons.IH unfolding trans_def by simp
    qed
    show ?thesis using deletes
      unfolding relative_adp_components_at_def by simp
  qed
  have strict_target: "(adp_combine_terms
      (relative_adp_components_at s (redex # ?pred @ leftovers)),
      relative_adp_term_annotation_summary t) \<in> S"
  proof -
    have first: "(adp_combine_terms
        (relative_adp_components_at s (redex # ?pred @ leftovers)),
      adp_combine_terms
        (relative_adp_components_at t (?fresh @ ?targets))) \<in> S"
      using compat_S_NS strict_replaced dropped_target
      unfolding relcomp_def by blast
    show ?thesis using compat_S_NS first target_permute
      unfolding relcomp_def by blast
  qed
  show ?thesis using compat_NS_S source_permute strict_target
    unfolding relcomp_def by blast
qed

lemma relative_adp_component_step_lift_fixed:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and applied:
      "relative_adp_applied_with P True s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
    and root_strict:
      "(map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)),
        adp_combine_terms (relative_adp_components_at t
          (relative_adp_fresh_target_positions_list pair redex))) \<in> S"
    and transported_weak: "list_all2 (\<lambda>q q'.
      (map_funs_term ADP_Symbol (mark_adp_root (s |_
          relative_adp_nonfresh_predecessor
            (relative_adp_fixed_nonredex_origin pair True redex phi sigma)
            s redex q')),
       map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
      (relative_adp_nonfresh_target_positions True pair redex t)
      (relative_adp_nonfresh_target_positions True pair redex t)"
  shows "(relative_adp_term_annotation_summary s,
      relative_adp_term_annotation_summary t) \<in> S"
proof (rule relative_adp_component_step_lift[
    OF order invariant discard
      relative_adp_applied_with_imp_applied_at[OF applied]])
  fix q'
  assume q': "q' \<in> set
    (relative_adp_nonfresh_target_positions True pair redex t)"
  then have target: "q' \<in> sharp_positions t"
    and nonfresh: "q' \<notin> relative_adp_fresh_positions True pair redex"
    unfolding relative_adp_nonfresh_target_positions_def
    using finite_relative_adp_sharp_positions[of t] by auto
  from relative_adp_fixed_nonfresh_covered[
      OF applied lhs_fun target nonfresh]
  obtain q where source: "q \<in> sharp_positions s" and neq: "q \<noteq> redex"
    and edge: "relative_adp_fixed_nonredex_origin pair True redex
      phi sigma q q'" .
  show "\<exists>q. q \<in> sharp_positions s \<and> q \<noteq> redex \<and>
      relative_adp_fixed_nonredex_origin pair True redex phi sigma q q'"
    using source neq edge by blast
next
  fix q a b
  assume "relative_adp_fixed_nonredex_origin pair True redex phi sigma q a"
    and "relative_adp_fixed_nonredex_origin pair True redex phi sigma q b"
  then show "a = b"
    by (rule relative_adp_fixed_nonredex_origin_functional)
next
  show "(map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)),
      adp_combine_terms (relative_adp_components_at t
        (relative_adp_fresh_target_positions_list pair redex))) \<in> S"
    by (rule root_strict)
next
  show "list_all2 (\<lambda>q q'.
      (map_funs_term ADP_Symbol (mark_adp_root
        (s |_ relative_adp_nonfresh_predecessor
          (relative_adp_fixed_nonredex_origin pair True redex phi sigma)
          s redex q')),
       map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
    (relative_adp_nonfresh_target_positions True pair redex t)
    (relative_adp_nonfresh_target_positions True pair redex t)"
    by (rule transported_weak)
qed

lemma relative_adp_component_step_lift_fixed_weak_marked:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and applied:
      "relative_adp_applied_with P True s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
    and root_weak:
      "(map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)),
        adp_combine_terms (relative_adp_components_at t
          (relative_adp_fresh_target_positions_list pair redex))) \<in> NS"
    and transported_weak: "list_all2 (\<lambda>q q'.
      (map_funs_term ADP_Symbol (mark_adp_root (s |_
          relative_adp_nonfresh_predecessor
            (relative_adp_fixed_nonredex_origin pair True redex phi sigma)
            s redex q')),
       map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
      (relative_adp_nonfresh_target_positions True pair redex t)
      (relative_adp_nonfresh_target_positions True pair redex t)"
  shows "(relative_adp_term_annotation_summary s,
      relative_adp_term_annotation_summary t) \<in> NS"
proof -
  interpret adp_com_redtriple_order S NS NST by (rule order)
  let ?origin =
    "relative_adp_fixed_nonredex_origin pair True redex phi sigma"
  let ?targets =
    "relative_adp_nonfresh_target_positions True pair redex t"
  let ?pred = "map (relative_adp_nonfresh_predecessor ?origin s redex)
    ?targets"
  let ?fresh = "relative_adp_fresh_target_positions_list pair redex"
  have covered: "\<And>q'. q' \<in> set ?targets \<Longrightarrow>
      \<exists>q. q \<in> sharp_positions s \<and> q \<noteq> redex \<and>
        ?origin q q'"
  proof -
    fix q'
    assume member: "q' \<in> set ?targets"
    then have target: "q' \<in> sharp_positions t"
      and nonfresh: "q' \<notin> relative_adp_fresh_positions True pair redex"
      unfolding relative_adp_nonfresh_target_positions_def
      using finite_relative_adp_sharp_positions[of t] by auto
    from relative_adp_fixed_nonfresh_covered[OF applied lhs_fun target nonfresh]
    show "\<exists>q. q \<in> sharp_positions s \<and> q \<noteq> redex \<and>
        ?origin q q'" by blast
  qed
  have functional: "\<And>q a b. ?origin q a \<Longrightarrow> ?origin q b \<Longrightarrow>
      a = b"
    by (rule relative_adp_fixed_nonredex_origin_functional)
  obtain leftovers where source_positions:
      "mset (redex # ?pred @ leftovers) =
        mset (sorted_list_of_set (sharp_positions s))"
    by (rule relative_adp_source_position_partition[
        OF relative_adp_applied_with_imp_applied_at[OF applied]
          covered functional])
  have source_components: "mset
      (relative_adp_components_at s (redex # ?pred @ leftovers)) =
    mset (relative_adp_term_annotation_components s)"
  proof -
    have mapped: "mset
        (relative_adp_components_at s (redex # ?pred @ leftovers)) =
      mset (relative_adp_components_at s
        (sorted_list_of_set (sharp_positions s)))"
      by (rule relative_adp_components_at_mset_cong[OF source_positions])
    show ?thesis using mapped unfolding relative_adp_term_annotation_components_def
      relative_adp_components_at_def .
  qed
  have source_permute: "(relative_adp_term_annotation_summary s,
      adp_combine_terms
        (relative_adp_components_at s (redex # ?pred @ leftovers))) \<in> NS"
    unfolding relative_adp_term_annotation_summary_def
    by (rule adp_combine_terms_permutation[
        OF refl_NS trans_NS ctxt_NS invariant])
       (use source_components in simp)
  have tails: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
      (relative_adp_components_at s (redex # ?pred @ leftovers))
      (adp_combine_terms (relative_adp_components_at t ?fresh) #
        (relative_adp_components_at t ?targets @
          map (\<lambda>p. Fun Com0 []) leftovers))"
  proof -
    have transported: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
        (relative_adp_components_at s ?pred)
        (relative_adp_components_at t ?targets)"
      using transported_weak unfolding relative_adp_components_at_def
      by (induction ?targets) auto
    have dropped: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
        (relative_adp_components_at s leftovers)
        (map (\<lambda>p. Fun Com0 []) leftovers)"
      using discard unfolding adp_com_discarding_def
        relative_adp_components_at_def by (induction leftovers) auto
    show ?thesis using root_weak list_all2_appendI[OF transported dropped]
      unfolding relative_adp_components_at_def by simp
  qed
  have combined: "(adp_combine_terms
        (relative_adp_components_at s (redex # ?pred @ leftovers)),
      adp_combine_terms
        (adp_combine_terms (relative_adp_components_at t ?fresh) #
          (relative_adp_components_at t ?targets @
            map (\<lambda>p. Fun Com0 []) leftovers))) \<in> NS"
    by (rule adp_combine_terms_list_all2[
        OF refl_NS trans_NS ctxt_NS tails])
  have packed: "(adp_combine_terms
        (adp_combine_terms (relative_adp_components_at t ?fresh) #
          (relative_adp_components_at t ?targets @
            map (\<lambda>p. Fun Com0 []) leftovers)),
      adp_combine_terms
        (relative_adp_components_at t (?fresh @ ?targets) @
          map (\<lambda>p. Fun Com0 []) leftovers)) \<in> NS"
    using adp_combine_terms_prepend_summary[
      OF refl_NS trans_NS ctxt_NS invariant discard,
      where xs="relative_adp_components_at t ?fresh" and
        ys="relative_adp_components_at t ?targets @
          map (\<lambda>p. Fun Com0 []) leftovers"]
    unfolding relative_adp_components_at_def by simp
  have deletes: "(adp_combine_terms
        (relative_adp_components_at t (?fresh @ ?targets) @
          map (\<lambda>p. Fun Com0 []) leftovers),
      adp_combine_terms (relative_adp_components_at t (?fresh @ ?targets)))
      \<in> NS"
  proof (induction leftovers)
    case Nil
    then show ?case using refl_NS unfolding refl_on_def by simp
  next
    case (Cons p ps)
    note one = adp_combine_terms_delete[OF ctxt_NS discard,
      where xs="relative_adp_components_at t (?fresh @ ?targets)" and
        x="Fun Com0 []" and ys="map (\<lambda>p. Fun Com0 []) ps"]
    show ?case using trans_NS one Cons.IH unfolding trans_def by simp
  qed
  have target_positions: "mset (?fresh @ ?targets) =
      mset (sorted_list_of_set (sharp_positions t))"
    by (rule relative_adp_target_position_partition[
        OF relative_adp_applied_with_imp_applied_at[OF applied]])
  have target_components: "mset (relative_adp_components_at t
      (?fresh @ ?targets)) = mset (relative_adp_term_annotation_components t)"
  proof -
    have mapped: "mset (relative_adp_components_at t (?fresh @ ?targets)) =
      mset (relative_adp_components_at t
        (sorted_list_of_set (sharp_positions t)))"
      by (rule relative_adp_components_at_mset_cong[OF target_positions])
    show ?thesis using mapped unfolding relative_adp_term_annotation_components_def
      relative_adp_components_at_def .
  qed
  have target_permute: "(adp_combine_terms
        (relative_adp_components_at t (?fresh @ ?targets)),
      relative_adp_term_annotation_summary t) \<in> NS"
    unfolding relative_adp_term_annotation_summary_def
    by (rule adp_combine_terms_permutation[
        OF refl_NS trans_NS ctxt_NS invariant])
       (use target_components in simp)
  show ?thesis using trans_NS source_permute combined packed deletes target_permute
    unfolding trans_def by blast
qed

lemma relative_adp_component_step_lift_fixed_weak_unmarked:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and applied:
      "relative_adp_applied_with P False s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
    and transported_weak: "list_all2 (\<lambda>q q'.
      (map_funs_term ADP_Symbol (mark_adp_root (s |_
          relative_adp_nonfresh_predecessor
            (relative_adp_fixed_nonredex_origin pair False redex phi sigma)
            s redex q')),
       map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
      (relative_adp_nonfresh_target_positions False pair redex t)
      (relative_adp_nonfresh_target_positions False pair redex t)"
  shows "(relative_adp_term_annotation_summary s,
      relative_adp_term_annotation_summary t) \<in> NS"
proof -
  interpret adp_com_redtriple_order S NS NST by (rule order)
  let ?origin =
    "relative_adp_fixed_nonredex_origin pair False redex phi sigma"
  let ?targets =
    "relative_adp_nonfresh_target_positions False pair redex t"
  let ?pred = "map (relative_adp_nonfresh_predecessor ?origin s redex)
    ?targets"
  have redex_unmarked: "redex \<notin> sharp_positions s"
    using applied unfolding relative_adp_applied_with_def by (cases pair) auto
  have covered: "\<And>q'. q' \<in> set ?targets \<Longrightarrow>
      \<exists>q. q \<in> sharp_positions s \<and> q \<noteq> redex \<and>
        ?origin q q'"
  proof -
    fix q'
    assume member: "q' \<in> set ?targets"
    then have target: "q' \<in> sharp_positions t"
      and nonfresh: "q' \<notin> relative_adp_fresh_positions False pair redex"
      unfolding relative_adp_nonfresh_target_positions_def
      using finite_relative_adp_sharp_positions[of t] by auto
    from relative_adp_fixed_nonfresh_covered[OF applied lhs_fun target nonfresh]
    show "\<exists>q. q \<in> sharp_positions s \<and> q \<noteq> redex \<and>
        ?origin q q'" by blast
  qed
  have functional: "\<And>q a b. ?origin q a \<Longrightarrow> ?origin q b \<Longrightarrow>
      a = b"
    by (rule relative_adp_fixed_nonredex_origin_functional)
  have pred_subset: "mset ?pred \<subseteq># mset
      (sorted_list_of_set (sharp_positions s - {redex}))"
  proof (rule relative_adp_nonfresh_components_multiset_subset[
      OF covered functional])
    show "distinct ?targets"
      unfolding relative_adp_nonfresh_target_positions_def
      by (rule distinct_filter, rule distinct_sorted_list_of_set)
  qed
  have source_rest: "sorted_list_of_set (sharp_positions s - {redex}) =
      sorted_list_of_set (sharp_positions s)"
    using redex_unmarked by simp
  from mset_le_perm_append[THEN iffD1, OF pred_subset]
  obtain leftovers where source_positions:
      "mset (?pred @ leftovers) =
        mset (sorted_list_of_set (sharp_positions s))"
    unfolding source_rest by blast
  have source_components: "mset
      (relative_adp_components_at s (?pred @ leftovers)) =
    mset (relative_adp_term_annotation_components s)"
  proof -
    have mapped: "mset (relative_adp_components_at s (?pred @ leftovers)) =
      mset (relative_adp_components_at s
        (sorted_list_of_set (sharp_positions s)))"
      by (rule relative_adp_components_at_mset_cong[OF source_positions])
    show ?thesis using mapped unfolding relative_adp_term_annotation_components_def
      relative_adp_components_at_def .
  qed
  have source_permute: "(relative_adp_term_annotation_summary s,
      adp_combine_terms (relative_adp_components_at s (?pred @ leftovers)))
      \<in> NS"
    unfolding relative_adp_term_annotation_summary_def
    by (rule adp_combine_terms_permutation[
        OF refl_NS trans_NS ctxt_NS invariant])
       (use source_components in simp)
  have transported: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
      (relative_adp_components_at s ?pred)
      (relative_adp_components_at t ?targets)"
    using transported_weak unfolding relative_adp_components_at_def
    by (induction ?targets) auto
  have dropped: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
      (relative_adp_components_at s leftovers)
      (map (\<lambda>p. Fun Com0 []) leftovers)"
    using discard unfolding adp_com_discarding_def
      relative_adp_components_at_def by (induction leftovers) auto
  have tails: "list_all2 (\<lambda>x y. (x,y) \<in> NS)
      (relative_adp_components_at s (?pred @ leftovers))
      (relative_adp_components_at t ?targets @
        map (\<lambda>p. Fun Com0 []) leftovers)"
    using list_all2_appendI[OF transported dropped]
    unfolding relative_adp_components_at_def by simp
  have combined: "(adp_combine_terms
        (relative_adp_components_at s (?pred @ leftovers)),
      adp_combine_terms (relative_adp_components_at t ?targets @
        map (\<lambda>p. Fun Com0 []) leftovers)) \<in> NS"
    by (rule adp_combine_terms_list_all2[
        OF refl_NS trans_NS ctxt_NS tails])
  have deletes: "(adp_combine_terms
        (relative_adp_components_at t ?targets @
          map (\<lambda>p. Fun Com0 []) leftovers),
      adp_combine_terms (relative_adp_components_at t ?targets)) \<in> NS"
  proof (induction leftovers)
    case Nil
    then show ?case using refl_NS unfolding refl_on_def by simp
  next
    case (Cons p ps)
    note one = adp_combine_terms_delete[OF ctxt_NS discard,
      where xs="relative_adp_components_at t ?targets" and
        x="Fun Com0 []" and ys="map (\<lambda>p. Fun Com0 []) ps"]
    show ?case using trans_NS one Cons.IH unfolding trans_def by simp
  qed
  have target_positions: "mset ?targets =
      mset (sorted_list_of_set (sharp_positions t))"
  proof -
    have sets: "set ?targets = sharp_positions t"
      unfolding relative_adp_nonfresh_target_positions_def
        relative_adp_fresh_positions_def
      using finite_relative_adp_sharp_positions[of t] by simp
    have d1: "distinct ?targets"
      unfolding relative_adp_nonfresh_target_positions_def by simp
    have d2: "distinct (sorted_list_of_set (sharp_positions t))" by simp
    have sets': "set ?targets =
        set (sorted_list_of_set (sharp_positions t))"
      using sets finite_relative_adp_sharp_positions[of t] by simp
    show ?thesis using set_eq_iff_mset_eq_distinct[OF d1 d2] sets' by blast
  qed
  have target_components: "mset (relative_adp_components_at t ?targets) =
      mset (relative_adp_term_annotation_components t)"
  proof -
    have mapped: "mset (relative_adp_components_at t ?targets) =
      mset (relative_adp_components_at t
        (sorted_list_of_set (sharp_positions t)))"
      by (rule relative_adp_components_at_mset_cong[OF target_positions])
    show ?thesis using mapped unfolding relative_adp_term_annotation_components_def
      relative_adp_components_at_def .
  qed
  have target_permute: "(adp_combine_terms
        (relative_adp_components_at t ?targets),
      relative_adp_term_annotation_summary t) \<in> NS"
    unfolding relative_adp_term_annotation_summary_def
    by (rule adp_combine_terms_permutation[
        OF refl_NS trans_NS ctxt_NS invariant])
       (use target_components in simp)
  show ?thesis using trans_NS source_permute combined deletes target_permute
    unfolding trans_def by blast
qed

lemma adp_step_case_has_applied_with_witness:
  assumes step: "adp_step_case P at_sharp s t"
  obtains pair redex phi sigma A where
    "relative_adp_applied_with P at_sharp s t pair redex phi sigma A"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  show thesis
  proof (rule that[of "(l,r)" p phi sigma A])
    show "relative_adp_applied_with P at_sharp s t (l,r) p phi sigma A"
      unfolding relative_adp_applied_with_def
      using adp_stepI by blast
  qed
qed

definition relative_adp_com_lhs ::
  "('f, 'v) adp \<Rightarrow> ('f adp_com_symbol, 'v) term" where
  "relative_adp_com_lhs pair =
    map_funs_term ADP_Symbol (mark_adp_root (fst pair))"

lemma relative_adp_fixed_root_source_instance:
  assumes applied:
      "relative_adp_applied_with P True s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
  shows "map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)) =
    relative_adp_com_lhs pair \<cdot>
      map_funs_subst (ADP_Symbol \<circ> adp_symbol.Plain) sigma"
proof -
  obtain l r where pair: "pair = (l,r)" by (cases pair)
  from applied have erased:
      "erase_adp_term (s |_ redex) = erase_adp_term l \<cdot> sigma"
    unfolding relative_adp_applied_with_def pair by simp
  have lhs_l: "is_Fun l" using lhs_fun unfolding pair by simp
  have marked: "mark_adp_root (s |_ redex) =
      mark_adp_root l \<cdot> (plain_adp_term \<circ> sigma)"
    by (rule mark_adp_root_erased_instance[OF lhs_l erased])
  show ?thesis unfolding relative_adp_com_lhs_def pair marked
    by (simp add: map_funs_subst_distrib map_funs_plain_adp_term
        comp_def fun_eq_iff)
qed

lemma relative_adp_fixed_fresh_component_instance:
  assumes applied:
      "relative_adp_applied_with P True s t pair redex phi sigma A"
    and alpha: "alpha \<in> sharp_positions (snd pair)"
  shows "map_funs_term ADP_Symbol
      (mark_adp_root (t |_ (redex @ alpha))) =
    map_funs_term ADP_Symbol (mark_adp_root (snd pair |_ alpha)) \<cdot>
      map_funs_subst (ADP_Symbol \<circ> adp_symbol.Plain) sigma"
proof -
  obtain l r where pair: "pair = (l,r)" by (cases pair)
  from applied have redex_fun: "redex \<in> fun_poss s"
    and annotations: "A = sharp_positions r \<union>
      transported_annotations phi l (s |_ redex)"
    and target: "t = replace_at s redex
      (annotate_term A (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_applied_with_def pair by auto
  have redex_poss: "redex \<in> poss s"
    by (rule fun_poss_imp_poss[OF redex_fun])
  have alpha_r: "alpha \<in> sharp_positions r" using alpha pair by simp
  have alpha_poss_r: "alpha \<in> poss r"
    using alpha_r unfolding sharp_positions_def by auto
  have alpha_poss_erased: "alpha \<in> poss (erase_adp_term r)"
    using alpha_poss_r poss_erase_adp_term by metis
  have alpha_poss_subst: "alpha \<in> poss (erase_adp_term r \<cdot> sigma)"
    using alpha_poss_erased by simp
  have alpha_A: "alpha \<in> A" using annotations alpha_r by simp
  have alpha_fun: "alpha \<in> fun_poss (erase_adp_term r \<cdot> sigma)"
  proof -
    have alpha_poss: "alpha \<in> poss r"
      using alpha_r unfolding sharp_positions_def by simp
    have alpha_is_fun: "is_Fun (r |_ alpha)"
      using alpha_r unfolding sharp_positions_def
      by (cases "r |_ alpha") auto
    have "alpha \<in> fun_poss r"
      by (rule poss_is_Fun_fun_poss[OF alpha_poss alpha_is_fun])
    then have "alpha \<in> fun_poss (erase_adp_term r)"
      using fun_poss_erase_adp_term by simp
    then show ?thesis using fun_poss_subst by blast
  qed
  have local: "t |_ (redex @ alpha) =
      annotate_term A (erase_adp_term r \<cdot> sigma) |_ alpha"
  proof -
    have redex_t: "redex \<in> poss t"
      unfolding target by (rule replace_at_below_poss[OF redex_poss]) simp
    have root: "t |_ redex =
        annotate_term A (erase_adp_term r \<cdot> sigma)"
      unfolding target by (rule replace_at_subt_at[OF redex_poss])
    show ?thesis unfolding subt_at_append[OF redex_t] root by simp
  qed
  have erased_local: "erase_adp_term (t |_ (redex @ alpha)) =
      erase_adp_term (r |_ alpha) \<cdot> sigma"
  proof -
    have alpha_poss_annotated: "alpha \<in>
        poss (annotate_term A (erase_adp_term r \<cdot> sigma))"
      using alpha_poss_subst unfolding annotate_term_def by simp
    have erased_annotation: "erase_adp_term
        (annotate_term A (erase_adp_term r \<cdot> sigma) |_ alpha) =
      (erase_adp_term r \<cdot> sigma) |_ alpha"
      using erase_annotate_term[of A "erase_adp_term r \<cdot> sigma"]
        erase_adp_term_subt_at[OF alpha_poss_annotated]
        poss_annotate_term_at[of A "[]" "erase_adp_term r \<cdot> sigma"]
      unfolding annotate_term_def by simp
    have subst_at: "(erase_adp_term r \<cdot> sigma) |_ alpha =
        erase_adp_term (r |_ alpha) \<cdot> sigma"
      using subt_at_subst[OF alpha_poss_erased, of sigma]
        erase_adp_term_subt_at[OF alpha_poss_r] by simp
    show ?thesis using local erased_annotation subst_at by simp
  qed
  have rhs_fun: "is_Fun (r |_ alpha)"
    using alpha_r unfolding sharp_positions_def
    by (auto split: option.splits prod.splits)
  have marked: "mark_adp_root (t |_ (redex @ alpha)) =
      mark_adp_root (r |_ alpha) \<cdot> (plain_adp_term \<circ> sigma)"
    by (rule mark_adp_root_erased_instance[OF rhs_fun erased_local])
  show ?thesis unfolding pair marked
    by (simp add: map_funs_subst_distrib map_funs_plain_adp_term
        comp_def fun_eq_iff)
qed

lemma adp_combine_terms_subst:
  "adp_combine_terms xs \<cdot> tau =
    adp_combine_terms (map (\<lambda>t. t \<cdot> tau) xs)"
  by (induction xs rule: adp_combine_terms.induct) simp_all

lemma relative_adp_fresh_components_instantiated_mset:
  assumes applied:
      "relative_adp_applied_with P True s t pair redex phi sigma A"
  defines "tau \<equiv>
      map_funs_subst (ADP_Symbol \<circ> adp_symbol.Plain) sigma"
  shows "mset (relative_adp_components_at t
      (relative_adp_fresh_target_positions_list pair redex)) =
    mset (map (\<lambda>u. map_funs_term ADP_Symbol (mark_adp_root u) \<cdot> tau)
      (annotated_rhs_subterms_list pair))"
proof -
  let ?positions = "sorted_list_of_set (sharp_positions (snd pair))"
  have position_set: "set ?positions = sharp_positions (snd pair)"
    using finite_relative_adp_sharp_positions[of "snd pair"] by simp
  have annotation_set: "set (annotated_rhs_subterms_list pair) =
      (\<lambda>alpha. snd pair |_ alpha) ` sharp_positions (snd pair)"
    unfolding annotated_rhs_subterms_list_sound annotated_rhs_subterms_def
    by blast
  have component_instance: "\<And>alpha. alpha \<in> set ?positions \<Longrightarrow>
      map_funs_term ADP_Symbol (mark_adp_root (t |_ (redex @ alpha))) =
      map_funs_term ADP_Symbol (mark_adp_root (snd pair |_ alpha)) \<cdot>
        map_funs_subst (ADP_Symbol \<circ> adp_symbol.Plain) sigma"
  proof -
    fix alpha
    assume "alpha \<in> set ?positions"
    then have sharp: "alpha \<in> sharp_positions (snd pair)"
      using finite_relative_adp_sharp_positions[of "snd pair"] by simp
    show "map_funs_term ADP_Symbol (mark_adp_root (t |_ (redex @ alpha))) =
        map_funs_term ADP_Symbol (mark_adp_root (snd pair |_ alpha)) \<cdot>
          map_funs_subst (ADP_Symbol \<circ> adp_symbol.Plain) sigma"
      by (fact relative_adp_fixed_fresh_component_instance[OF applied sharp])
  qed
  have fresh_map: "relative_adp_components_at t
      (relative_adp_fresh_target_positions_list pair redex) =
    map (\<lambda>alpha. map_funs_term ADP_Symbol
      (mark_adp_root (snd pair |_ alpha)) \<cdot>
        map_funs_subst (ADP_Symbol \<circ> adp_symbol.Plain) sigma) ?positions"
    unfolding relative_adp_components_at_def
      relative_adp_fresh_target_positions_list_def
    using component_instance by simp
  have positions_mset: "mset ?positions = mset
      (filter (\<lambda>q. case Term.root (snd pair |_ q) of
          None \<Rightarrow> False | Some (f,n) \<Rightarrow> is_sharp_symbol f)
        (poss_list (snd pair)))"
  proof -
    have rhs_set: "set (filter (\<lambda>q. case Term.root (snd pair |_ q) of
          None \<Rightarrow> False | Some (f,n) \<Rightarrow> is_sharp_symbol f)
        (poss_list (snd pair))) = sharp_positions (snd pair)"
      unfolding sharp_positions_def by (auto simp: poss_list_sound)
    have rhs_distinct: "distinct (filter (\<lambda>q.
        case Term.root (snd pair |_ q) of None \<Rightarrow> False
          | Some (f,n) \<Rightarrow> is_sharp_symbol f)
        (poss_list (snd pair)))"
      by (rule distinct_filter[OF distinct_relative_adp_poss_list])
    show ?thesis using set_eq_iff_mset_eq_distinct[OF _ rhs_distinct]
      position_set rhs_set by simp
  qed
  show ?thesis
    unfolding fresh_map annotated_rhs_subterms_list_def
    using arg_cong[OF positions_mset,
      where f="image_mset (\<lambda>alpha. map_funs_term ADP_Symbol
        (mark_adp_root (snd pair |_ alpha)) \<cdot> tau)"]
    by (simp add: tau_def comp_def)
qed

lemma relative_adp_fixed_root_strict_from_constraint:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and applied:
      "relative_adp_applied_with P True s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
    and constraint:
      "(relative_adp_com_lhs pair,
        relative_adp_annotation_summary pair) \<in> S"
  shows "(map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)),
      adp_combine_terms (relative_adp_components_at t
        (relative_adp_fresh_target_positions_list pair redex))) \<in> S"
proof -
  interpret adp_com_redtriple_order S NS NST by (rule order)
  let ?tau = "map_funs_subst
    (ADP_Symbol \<circ> adp_symbol.Plain) sigma"
  let ?finite = "map (\<lambda>u.
    map_funs_term ADP_Symbol (mark_adp_root u) \<cdot> ?tau)
    (annotated_rhs_subterms_list pair)"
  let ?actual = "relative_adp_components_at t
    (relative_adp_fresh_target_positions_list pair redex)"
  have instantiated: "(relative_adp_com_lhs pair \<cdot> ?tau,
      relative_adp_annotation_summary pair \<cdot> ?tau) \<in> S"
    using subst_S constraint unfolding subst.closed_def by blast
  have source: "map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)) =
      relative_adp_com_lhs pair \<cdot> ?tau"
    by (rule relative_adp_fixed_root_source_instance[OF applied lhs_fun])
  have rhs: "relative_adp_annotation_summary pair \<cdot> ?tau =
      adp_combine_terms ?finite"
    unfolding relative_adp_annotation_summary_def adp_combine_terms_subst
    by (simp add: map_funs_plain_adp_term comp_def)
  have finite_strict: "(map_funs_term ADP_Symbol
        (mark_adp_root (s |_ redex)), adp_combine_terms ?finite) \<in> S"
    using instantiated unfolding source rhs .
  have mset: "mset ?actual = mset ?finite"
    by (rule relative_adp_fresh_components_instantiated_mset[OF applied])
  have permuted: "(adp_combine_terms ?finite,
      adp_combine_terms ?actual) \<in> NS"
    by (rule adp_combine_terms_permutation[
        OF refl_NS trans_NS ctxt_NS invariant]) (use mset in simp)
  show ?thesis using compat_S_NS finite_strict permuted
    unfolding relcomp_def by blast
qed

lemma relative_adp_fixed_root_weak_from_constraint:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and applied:
      "relative_adp_applied_with P True s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
    and constraint:
      "(relative_adp_com_lhs pair,
        relative_adp_annotation_summary pair) \<in> NS"
  shows "(map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)),
      adp_combine_terms (relative_adp_components_at t
        (relative_adp_fresh_target_positions_list pair redex))) \<in> NS"
proof -
  interpret adp_com_redtriple_order S NS NST by (rule order)
  let ?tau = "map_funs_subst
    (ADP_Symbol \<circ> adp_symbol.Plain) sigma"
  let ?finite = "map (\<lambda>u.
    map_funs_term ADP_Symbol (mark_adp_root u) \<cdot> ?tau)
    (annotated_rhs_subterms_list pair)"
  let ?actual = "relative_adp_components_at t
    (relative_adp_fresh_target_positions_list pair redex)"
  have instantiated: "(relative_adp_com_lhs pair \<cdot> ?tau,
      relative_adp_annotation_summary pair \<cdot> ?tau) \<in> NS"
    using subst_NS constraint unfolding subst.closed_def by blast
  have source: "map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)) =
      relative_adp_com_lhs pair \<cdot> ?tau"
    by (rule relative_adp_fixed_root_source_instance[OF applied lhs_fun])
  have rhs: "relative_adp_annotation_summary pair \<cdot> ?tau =
      adp_combine_terms ?finite"
    unfolding relative_adp_annotation_summary_def adp_combine_terms_subst
    by (simp add: map_funs_plain_adp_term comp_def)
  have finite_weak: "(map_funs_term ADP_Symbol
        (mark_adp_root (s |_ redex)), adp_combine_terms ?finite) \<in> NS"
    using instantiated unfolding source rhs .
  have mset: "mset ?actual = mset ?finite"
    by (rule relative_adp_fresh_components_instantiated_mset[OF applied])
  have permuted: "(adp_combine_terms ?finite,
      adp_combine_terms ?actual) \<in> NS"
    by (rule adp_combine_terms_permutation[
        OF refl_NS trans_NS ctxt_NS invariant]) (use mset in simp)
  show ?thesis using trans_NS finite_weak permuted unfolding trans_def by blast
qed

lemma relative_adp_fixed_origin_canonical:
  assumes applied:
      "relative_adp_applied_with P at_sharp s t pair redex phi sigma A"
    and edge: "relative_adp_fixed_nonredex_origin pair at_sharp redex
      phi sigma q q'"
  shows "relative_adp_canonical_origin_edge P at_sharp s t pair redex q q'"
proof -
  obtain l r where pair: "pair = (l,r)" by (cases pair)
  from applied have data:
      "(l,r) \<in> P" "plain_adp_term_pred l" "valid_vrf (l,r) phi"
      "redex \<in> fun_poss s"
      "at_sharp = (redex \<in> sharp_positions s)"
      "erase_adp_term (s |_ redex) = erase_adp_term l \<cdot> sigma"
      "A = (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ redex)"
      "t = replace_at s redex
        (annotate_term A (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_applied_with_def pair by auto
  from edge have origin: "origin_edge (erase_adp_term l)
      (erase_adp_term r) redex sigma
      (if at_sharp then sharp_positions r else {}) phi q q'"
    using edge unfolding relative_adp_fixed_nonredex_origin_def pair
    by (cases at_sharp) auto
  show ?thesis unfolding relative_adp_canonical_origin_edge_def
    apply (intro exI conjI)
    using pair data origin by auto
qed

lemma relative_adp_fixed_nonredex_projection:
  assumes applied:
      "relative_adp_applied_with P at_sharp s t pair redex phi sigma A"
    and edge: "relative_adp_fixed_nonredex_origin pair at_sharp redex
      phi sigma q q'"
    and source_sharp: "q \<in> sharp_positions s"
  shows "(mark_adp_root (s |_ q), mark_adp_root (t |_ q')) \<in>
    (adp_step_case_rel {erase_annotations_adp pair} False)\<^sup>*"
proof -
  obtain l r where pair: "pair = (l,r)" by (cases pair)
  from applied have valid: "valid_vrf (l,r) phi"
    and redex_fun: "redex \<in> fun_poss s"
    and lhs: "erase_adp_term (s |_ redex) = erase_adp_term l \<cdot> sigma"
    and target: "t = replace_at s redex
      (annotate_term A (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_applied_with_def pair by auto
  have canonical: "relative_adp_canonical_origin_edge P at_sharp s t
      pair redex q q'"
    by (rule relative_adp_fixed_origin_canonical[OF applied edge])
  from edge have nonredex: "q \<noteq> redex"
    unfolding relative_adp_fixed_nonredex_origin_def by simp
  have nonredex': "redex \<noteq> q" using nonredex by simp
  have alternative: "(q' = q \<and> (q <\<^sub>p redex \<or> q \<bottom> redex)) \<or>
      erase_adp_term (s |_ q) = erase_adp_term (t |_ q')"
    using canonical nonredex'
    by (rule relative_adp_canonical_origin_projection)
  have q_poss: "q \<in> poss s"
    using source_sharp unfolding sharp_positions_def by auto
  from alternative show ?thesis
  proof
    assume preserved: "q' = q \<and> (q <\<^sub>p redex \<or> q \<bottom> redex)"
    then have q': "q' = q" and outside: "q <\<^sub>p redex \<or> q \<bottom> redex"
      by auto
    from outside show ?thesis
    proof
      assume above: "q <\<^sub>p redex"
      from prefixE[OF prefix_order.less_imp_le[OF above]]
      obtain delta where redex: "redex = q @ delta" by blast
      have nonroot: "delta \<noteq> []" using above redex by auto
      have delta_fun: "delta \<in> fun_poss (s |_ q)"
      proof -
        have delta_poss: "delta \<in> poss (s |_ q)"
          using fun_poss_imp_poss[OF redex_fun] q_poss redex by simp
        from fun_poss_fun_conv[OF redex_fun]
        obtain f ts where at: "s |_ redex = Fun f ts" by blast
        have at_delta: "s |_ q |_ delta = Fun f ts"
          using at redex q_poss by simp
        have delta_is_fun: "is_Fun (s |_ q |_ delta)"
          unfolding at_delta by simp
        show ?thesis by (rule poss_is_Fun_fun_poss[OF delta_poss delta_is_fun])
      qed
      have delta_fun_erased: "delta \<in> fun_poss (erase_adp_term (s |_ q))"
        using delta_fun fun_poss_erase_adp_term[of "s |_ q"] by simp
      have delta_poss: "delta \<in> poss (s |_ q)"
        by (rule fun_poss_imp_poss[OF delta_fun])
      have local_redex: "erase_adp_term (s |_ q) |_ delta =
          erase_adp_term l \<cdot> sigma"
        using lhs redex q_poss delta_poss
          erase_adp_term_subt_at[OF q_poss]
          erase_adp_term_subt_at[OF delta_poss] by simp
      have marked_source: "mark_adp_root (s |_ q) =
          annotate_term {[]} (erase_adp_term (s |_ q))"
        unfolding mark_adp_root_def annotate_term_def by simp
      have raw_weak_step: "(annotate_term {[]} (erase_adp_term (s |_ q)),
          annotate_term {[]} (replace_at (erase_adp_term (s |_ q)) delta
            (erase_adp_term r \<cdot> sigma))) \<in>
        adp_step_case_rel (erase_annotations_adp ` {(l,r)}) False"
      proof (rule annotate_single_root_below_adp_step[
          where A="{(l,r)}" and l=l and r=r and phi=phi and delta=delta and
            u="erase_adp_term (s |_ q)" and sigma=sigma])
        show "(l,r) \<in> {(l,r)}" by simp
        show "valid_vrf (l,r) phi" by (rule valid)
        show "delta \<in> fun_poss (erase_adp_term (s |_ q))"
          by (rule delta_fun_erased)
        show "delta \<noteq> []" by (rule nonroot)
        show "erase_adp_term (s |_ q) |_ delta = erase_adp_term l \<cdot> sigma"
          by (rule local_redex)
      qed
      have weak_step: "(mark_adp_root (s |_ q),
          annotate_term {[]} (replace_at (erase_adp_term (s |_ q)) delta
            (erase_adp_term r \<cdot> sigma))) \<in>
        adp_step_case_rel {erase_annotations_adp pair} False"
        using raw_weak_step unfolding marked_source pair by simp
      have target_nested: "t = replace_at s q
          (replace_at (s |_ q) delta
            (annotate_term A (erase_adp_term r \<cdot> sigma)))"
        using target redex replace_at_append_context[OF q_poss,
          of delta "annotate_term A (erase_adp_term r \<cdot> sigma)"] by simp
      have target_q: "t |_ q = replace_at (s |_ q) delta
          (annotate_term A (erase_adp_term r \<cdot> sigma))"
        unfolding target_nested by (rule replace_at_subt_at[OF q_poss])
      have target_erased: "erase_adp_term (t |_ q) =
          replace_at (erase_adp_term (s |_ q)) delta
            (erase_adp_term r \<cdot> sigma)"
        using arg_cong[OF target_q, of erase_adp_term] delta_poss
        by (simp add: erase_adp_term_replace_at)
      have target_mark: "mark_adp_root (t |_ q) =
          annotate_term {[]} (replace_at (erase_adp_term (s |_ q)) delta
            (erase_adp_term r \<cdot> sigma))"
        unfolding mark_adp_root_def target_erased by simp
      show ?thesis unfolding q' target_mark by (rule r_into_rtrancl[OF weak_step])
    next
      assume parallel: "q \<bottom> redex"
      have same: "t |_ q = s |_ q"
        unfolding target
        by (rule parallel_replace_at_subt_at[
          OF parallel_pos_sym[OF parallel]
            fun_poss_imp_poss[OF redex_fun] q_poss])
      show ?thesis unfolding q' same by simp
    qed
  next
    assume erased: "erase_adp_term (s |_ q) = erase_adp_term (t |_ q')"
    then have "mark_adp_root (s |_ q) = mark_adp_root (t |_ q')"
      unfolding mark_adp_root_def by simp
    then show ?thesis by simp
  qed
qed

definition relative_adp_com_flat_rule ::
  "('f, 'v) adp \<Rightarrow> ('f adp_com_symbol, 'v) rule" where
  "relative_adp_com_flat_rule pair =
    map_funs_rule ADP_Symbol (erase_annotations_adp pair)"

lemma relative_adp_fixed_nonfresh_weak_from_constraint:
  assumes order: "adp_com_redtriple_order S NS NST"
    and applied:
      "relative_adp_applied_with P at_sharp s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
    and target: "q' \<in> sharp_positions t"
    and nonfresh:
      "q' \<notin> relative_adp_fresh_positions at_sharp pair redex"
    and constraint: "relative_adp_com_flat_rule pair \<in> NS"
  shows "(map_funs_term ADP_Symbol (mark_adp_root (s |_
      relative_adp_nonfresh_predecessor
        (relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma)
        s redex q')),
    map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS"
proof -
  interpret adp_com_redtriple_order S NS NST by (rule order)
  let ?origin =
    "relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma"
  let ?q = "relative_adp_nonfresh_predecessor ?origin s redex q'"
  from relative_adp_fixed_nonfresh_covered[OF applied lhs_fun target nonfresh]
  obtain source where source: "source \<in> sharp_positions s"
    and neq: "source \<noteq> redex" and edge: "?origin source q'" .
  have covered: "\<exists>source. source \<in> sharp_positions s \<and>
      source \<noteq> redex \<and> ?origin source q'"
    using source neq edge by blast
  have q_source: "?q \<in> sharp_positions s"
    by (rule relative_adp_nonfresh_predecessor_sound(1)[
        where origin="relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma"
          and s=s and redex=redex and q'=q', OF covered])
  have q_edge: "?origin ?q q'"
    by (rule relative_adp_nonfresh_predecessor_sound(3)[
        where origin="relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma"
          and s=s and redex=redex and q'=q', OF covered])
  have projected: "(mark_adp_root (s |_ ?q), mark_adp_root (t |_ q')) \<in>
      (adp_step_case_rel {erase_annotations_adp pair} False)\<^sup>*"
    by (rule relative_adp_fixed_nonredex_projection[
        OF applied q_edge q_source])
  have flat_set: "relative_adp_flat_rules {pair} =
      {erase_annotations_adp pair}"
    unfolding relative_adp_flat_rules_def by simp
  have projected': "(mark_adp_root (s |_ ?q), mark_adp_root (t |_ q')) \<in>
      (adp_step_case_rel (relative_adp_flat_rules {pair}) False)\<^sup>*"
    using projected unfolding flat_set .
  have rewrite_steps: "(mark_adp_root (s |_ ?q), mark_adp_root (t |_ q')) \<in>
      (rstep {erase_annotations_adp pair})\<^sup>*"
  proof -
    have source_eq: "mark_adp_root (s |_ ?q) = mark_adp_root (s |_ ?q)"
      by simp
    show ?thesis using relative_adp_flat_steps_are_rsteps[
      OF projected' source_eq] unfolding flat_set .
  qed
  have mapped: "(map_funs_term ADP_Symbol (mark_adp_root (s |_ ?q)),
      map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in>
    (rstep {relative_adp_com_flat_rule pair})\<^sup>*"
    using rsteps_imp_map_rsteps[OF rewrite_steps, of ADP_Symbol]
    unfolding relative_adp_com_flat_rule_def map_funs_trs.simps by simp
  have steps_NS: "rstep {relative_adp_com_flat_rule pair} \<subseteq> NS"
    by (rule rstep_subset[OF ctxt_NS subst_NS]) (use constraint in simp)
  show ?thesis using mapped
  proof (induction rule: rtrancl_induct)
    case base
    then show ?case using refl_NS unfolding refl_on_def by simp
  next
    case (step y z)
    have yz: "(y,z) \<in> NS"
      by (rule subsetD[OF steps_NS step.hyps(2)])
    show ?case using trans_NS step.IH yz unfolding trans_def by blast
  qed
qed

lemma relative_adp_fixed_transport_list_weak:
  assumes order: "adp_com_redtriple_order S NS NST"
    and applied:
      "relative_adp_applied_with P at_sharp s t pair redex phi sigma A"
    and lhs_fun: "is_Fun (fst pair)"
    and flat_weak: "relative_adp_com_flat_rule pair \<in> NS"
  shows "list_all2 (\<lambda>q q'.
      (map_funs_term ADP_Symbol (mark_adp_root (s |_
          relative_adp_nonfresh_predecessor
            (relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma)
            s redex q')),
       map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
    (relative_adp_nonfresh_target_positions at_sharp pair redex t)
    (relative_adp_nonfresh_target_positions at_sharp pair redex t)"
proof -
  let ?targets =
    "relative_adp_nonfresh_target_positions at_sharp pair redex t"
  have member: "q \<in> sharp_positions t \<and>
      q \<notin> relative_adp_fresh_positions at_sharp pair redex"
    if "q \<in> set ?targets" for q
    using that finite_relative_adp_sharp_positions[of t]
    unfolding relative_adp_nonfresh_target_positions_def by auto
  show ?thesis unfolding list_all2_same
  proof (intro ballI)
    fix q
    assume q: "q \<in> set ?targets"
    have target: "q \<in> sharp_positions t"
      and nonfresh:
        "q \<notin> relative_adp_fresh_positions at_sharp pair redex"
      using member[OF q] by auto
    have weak: "(map_funs_term ADP_Symbol (mark_adp_root (s |_
        relative_adp_nonfresh_predecessor
          (relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma)
          s redex q)),
      map_funs_term ADP_Symbol (mark_adp_root (t |_ q))) \<in> NS"
    proof (cases at_sharp)
      case True
      show ?thesis using relative_adp_fixed_nonfresh_weak_from_constraint[
        OF order applied[unfolded True] lhs_fun target nonfresh flat_weak]
        unfolding True .
    next
      case False
      show ?thesis using relative_adp_fixed_nonfresh_weak_from_constraint[
        OF order applied[unfolded False] lhs_fun target nonfresh flat_weak]
        unfolding False .
    qed
    show "(map_funs_term ADP_Symbol (mark_adp_root (s |_
        relative_adp_nonfresh_predecessor
          (relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma)
          s redex q)),
      map_funs_term ADP_Symbol (mark_adp_root (t |_ q))) \<in> NS"
      by (rule weak)
  qed
qed

lemma relative_adp_com_all_step_weak:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and lhs_fun: "\<And>pair. pair \<in> problem \<Longrightarrow> is_Fun (fst pair)"
    and flat_weak: "\<And>pair. pair \<in> problem \<Longrightarrow>
      relative_adp_com_flat_rule pair \<in> NS"
    and com_weak: "\<And>pair. pair \<in> problem \<Longrightarrow>
      (relative_adp_com_lhs pair,
       relative_adp_annotation_summary pair) \<in> NS"
    and step: "(s,t) \<in> adp_step problem"
  shows "(relative_adp_term_annotation_summary s,
      relative_adp_term_annotation_summary t) \<in> NS"
proof -
  from step obtain at_sharp where case_step:
      "adp_step_case problem at_sharp s t"
    unfolding adp_step_def adp_step_case_rel_def by auto
  from adp_step_case_has_applied_with_witness[OF case_step]
  obtain pair redex phi sigma A where applied:
      "relative_adp_applied_with problem at_sharp s t pair redex phi sigma A" .
  from applied have pair: "pair \<in> problem"
    unfolding relative_adp_applied_with_def by (cases pair) auto
  note transport_lemma = relative_adp_fixed_transport_list_weak[
      where S=S and NS=NS and NST=NST and P=problem and
        at_sharp=at_sharp and s=s and t=t and pair=pair and redex=redex and
        phi=phi and sigma=sigma and A=A]
  have transport: "list_all2 (\<lambda>q q'.
      (map_funs_term ADP_Symbol (mark_adp_root (s |_
          relative_adp_nonfresh_predecessor
            (relative_adp_fixed_nonredex_origin pair at_sharp redex phi sigma)
            s redex q')),
       map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
    (relative_adp_nonfresh_target_positions at_sharp pair redex t)
    (relative_adp_nonfresh_target_positions at_sharp pair redex t)"
  proof (rule transport_lemma)
    show "adp_com_redtriple_order S NS NST" by (rule order)
    show "relative_adp_applied_with problem at_sharp s t pair redex phi sigma A"
      by (rule applied)
    show "is_Fun (fst pair)" by (rule lhs_fun[OF pair])
    show "relative_adp_com_flat_rule pair \<in> NS" by (rule flat_weak[OF pair])
  qed
  show ?thesis
  proof (cases at_sharp)
    case True
    have applied_true:
        "relative_adp_applied_with problem True s t pair redex phi sigma A"
      using applied True by simp
    have root: "(map_funs_term ADP_Symbol
          (mark_adp_root (s |_ redex)),
        adp_combine_terms (relative_adp_components_at t
          (relative_adp_fresh_target_positions_list pair redex))) \<in> NS"
      by (rule relative_adp_fixed_root_weak_from_constraint[
          OF order invariant applied_true lhs_fun[OF pair] com_weak[OF pair]])
    have transport_true: "list_all2 (\<lambda>q q'.
        (map_funs_term ADP_Symbol (mark_adp_root (s |_
            relative_adp_nonfresh_predecessor
              (relative_adp_fixed_nonredex_origin pair True redex phi sigma)
              s redex q')),
         map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
      (relative_adp_nonfresh_target_positions True pair redex t)
      (relative_adp_nonfresh_target_positions True pair redex t)"
      using transport True by simp
    show ?thesis
      by (rule relative_adp_component_step_lift_fixed_weak_marked[
          OF order invariant discard applied_true lhs_fun[OF pair] root
            transport_true])
  next
    case False
    have applied_false:
        "relative_adp_applied_with problem False s t pair redex phi sigma A"
      using applied False by simp
    have transport_false: "list_all2 (\<lambda>q q'.
        (map_funs_term ADP_Symbol (mark_adp_root (s |_
            relative_adp_nonfresh_predecessor
              (relative_adp_fixed_nonredex_origin pair False redex phi sigma)
              s redex q')),
         map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
      (relative_adp_nonfresh_target_positions False pair redex t)
      (relative_adp_nonfresh_target_positions False pair redex t)"
      using transport False by simp
    show ?thesis
      by (rule relative_adp_component_step_lift_fixed_weak_unmarked[
          OF order invariant discard applied_false lhs_fun[OF pair]
            transport_false])
  qed
qed

lemma relative_adp_com_selected_step_strict:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and lhs_fun: "\<And>pair. pair \<in> problem \<Longrightarrow> is_Fun (fst pair)"
    and flat_weak: "\<And>pair. pair \<in> problem \<Longrightarrow>
      relative_adp_com_flat_rule pair \<in> NS"
    and selected_strict: "\<And>pair. pair \<in> selected \<Longrightarrow>
      (relative_adp_com_lhs pair,
       relative_adp_annotation_summary pair) \<in> S"
    and subset: "selected \<subseteq> problem"
    and step: "(s,t) \<in> adp_step_case_rel selected True"
  shows "(relative_adp_term_annotation_summary s,
      relative_adp_term_annotation_summary t) \<in> S"
proof -
  from step have case_step: "adp_step_case selected True s t"
    unfolding adp_step_case_rel_def by simp
  from adp_step_case_has_applied_with_witness[OF case_step]
  obtain pair redex phi sigma A where applied_selected:
      "relative_adp_applied_with selected True s t pair redex phi sigma A" .
  from applied_selected have pair_selected: "pair \<in> selected"
    unfolding relative_adp_applied_with_def by (cases pair) auto
  have pair_problem: "pair \<in> problem" using subset pair_selected by blast
  have applied: "relative_adp_applied_with problem True s t pair redex
      phi sigma A"
    using applied_selected subset unfolding relative_adp_applied_with_def
    by (cases pair) auto
  have root: "(map_funs_term ADP_Symbol (mark_adp_root (s |_ redex)),
      adp_combine_terms (relative_adp_components_at t
        (relative_adp_fresh_target_positions_list pair redex))) \<in> S"
    by (rule relative_adp_fixed_root_strict_from_constraint[
        OF order invariant applied lhs_fun[OF pair_problem]
          selected_strict[OF pair_selected]])
  have transport: "list_all2 (\<lambda>q q'.
      (map_funs_term ADP_Symbol (mark_adp_root (s |_
          relative_adp_nonfresh_predecessor
            (relative_adp_fixed_nonredex_origin pair True redex phi sigma)
            s redex q')),
       map_funs_term ADP_Symbol (mark_adp_root (t |_ q'))) \<in> NS)
    (relative_adp_nonfresh_target_positions True pair redex t)
    (relative_adp_nonfresh_target_positions True pair redex t)"
    by (rule relative_adp_fixed_transport_list_weak[
        OF order applied lhs_fun[OF pair_problem] flat_weak[OF pair_problem]])
  show ?thesis by (rule relative_adp_component_step_lift_fixed[
      OF order invariant discard applied lhs_fun[OF pair_problem] root transport])
qed

lemma plain_adp_term_pred_roundtrip:
  assumes "plain_adp_term_pred t"
  shows "plain_adp_term (erase_adp_term t) = t"
  using assms
  by (induction t) (auto simp: list_all_iff map_idI)

lemma relative_adp_flatten_preserves_plain_step:
  assumes step: "adp_step_case A False s t"
  shows "adp_step_case (erase_annotations_adp ` A) False s t"
  using step
proof cases
  case (adp_stepI l r phi p sigma annotations)
  let ?pair = "erase_annotations_adp (l,r)"
  have pair: "?pair \<in> erase_annotations_adp ` A"
    using adp_stepI(1) by blast
  have plain: "plain_adp_term_pred (fst ?pair)"
    unfolding erase_annotations_adp_def by simp
  have valid: "valid_vrf ?pair phi"
    by (rule valid_vrf_erase_annotations_adp[OF adp_stepI(3)])
  have lhs_roundtrip: "plain_adp_term (erase_adp_term l) = l"
    by (rule plain_adp_term_pred_roundtrip[OF adp_stepI(2)])
  have fst_pair: "fst ?pair = l"
    unfolding erase_annotations_adp_def using lhs_roundtrip by simp
  have lhs: "erase_adp_term (s |_ p) =
      erase_adp_term (fst ?pair) \<cdot> sigma"
    using adp_stepI(6) unfolding erase_annotations_adp_def by simp
  have annotation_eq: "annotations =
      (if False then sharp_positions (snd ?pair) else {}) \<union>
        transported_annotations phi (fst ?pair) (s |_ p)"
    using adp_stepI(7) fst_pair by simp
  have target: "t = replace_at s p
      (annotate_term annotations
        (erase_adp_term (snd ?pair) \<cdot> sigma))"
    using adp_stepI(8) unfolding erase_annotations_adp_def by simp
  show ?thesis
    apply (rule adp_step_case.adp_stepI[
      where l="fst ?pair" and r="snd ?pair" and phi=phi and p=p
        and sigma=sigma and A=annotations])
    subgoal using pair by simp
    subgoal by (fact plain)
    subgoal using valid by simp
    subgoal by (fact adp_stepI(4))
    subgoal by (fact adp_stepI(5))
    subgoal by (fact lhs)
    subgoal by (fact annotation_eq)
    subgoal by (fact target)
    done
qed

lemma relative_adp_plain_selected_step_in_residual:
  assumes step: "(s,t) \<in> adp_step_case_rel A False"
  shows "(s,t) \<in> adp_step (erase_annotations_adp ` A)"
proof -
  from step have "adp_step_case A False s t"
    unfolding adp_step_case_rel_def by simp
  then have "adp_step_case (erase_annotations_adp ` A) False s t"
    by (rule relative_adp_flatten_preserves_plain_step)
  then show ?thesis
    unfolding adp_step_def adp_step_case_rel_def by blast
qed

lemma relative_adp_main_without_selected_strict:
  "adp_step_case_rel P True - adp_step_case_rel A True \<subseteq>
    adp_step_case_rel (P - A) True"
proof -
  have "P = (P - A) \<union> (P \<inter> A)" by blast
  then have split: "adp_step_case_rel P True =
      adp_step_case_rel (P - A) True \<union>
      adp_step_case_rel (P \<inter> A) True"
    by (metis adp_step_case_rel_union)
  have "adp_step_case_rel (P \<inter> A) True \<subseteq>
      adp_step_case_rel A True"
    by (rule adp_step_case_rel_mono) blast
  with split show ?thesis by blast
qed

lemma relative_adp_steps_without_selected_strict:
  "adp_step (P \<union> B) - adp_step_case_rel A True \<subseteq>
    adp_step ((P - A) \<union> ((B - A) \<union>
      erase_annotations_adp ` A))"
proof
  fix step
  assume member: "step \<in>
      adp_step (P \<union> B) - adp_step_case_rel A True"
  obtain s t where step_eq: "step = (s,t)" by (cases step)
  from member step_eq obtain at_sharp where original:
      "adp_step_case (P \<union> B) at_sharp s t"
    unfolding adp_step_def adp_step_case_rel_def by auto
  from original obtain l r phi p sigma annotations where
      pair: "(l,r) \<in> P \<union> B"
    and plain: "plain_adp_term_pred l"
    and valid: "valid_vrf (l,r) phi"
    and redex: "p \<in> fun_poss s"
    and at: "at_sharp = (p \<in> sharp_positions s)"
    and lhs: "erase_adp_term (s |_ p) = erase_adp_term l \<cdot> sigma"
    and annotations: "annotations =
      (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ p)"
    and target: "t = replace_at s p
      (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    by cases blast
  show "step \<in> adp_step ((P - A) \<union> ((B - A) \<union>
      erase_annotations_adp ` A))"
  proof (cases "(l,r) \<in> A")
    case False
    have residual_pair: "(l,r) \<in>
        ((P - A) \<union> ((B - A) \<union> erase_annotations_adp ` A))"
      using pair False by blast
    have "adp_step_case
        ((P - A) \<union> ((B - A) \<union> erase_annotations_adp ` A))
        at_sharp s t"
      by (rule adp_step_case.adp_stepI[
          OF residual_pair plain valid redex at lhs annotations target])
    then show ?thesis unfolding step_eq adp_step_def adp_step_case_rel_def
      by (cases at_sharp) auto
  next
    case True
    have not_strict: "(s,t) \<notin> adp_step_case_rel A True"
      using member step_eq by simp
    have not_at_sharp: "at_sharp = False"
    proof (rule ccontr)
      assume "at_sharp \<noteq> False"
      then have "at_sharp = True" by simp
      moreover have "adp_step_case A at_sharp s t"
        by (rule adp_step_case.adp_stepI[
          OF True plain valid redex at lhs annotations target])
      ultimately have "adp_step_case A True s t" by simp
      with not_strict show False unfolding adp_step_case_rel_def by simp
    qed
    have "adp_step_case A False s t"
      by (rule adp_step_case.adp_stepI[
        OF True plain valid redex], use at lhs annotations target not_at_sharp in simp_all)
    then have "(s,t) \<in> adp_step_case_rel A False"
      unfolding adp_step_case_rel_def by simp
    then have "(s,t) \<in> adp_step (erase_annotations_adp ` A)"
      by (rule relative_adp_plain_selected_step_in_residual)
    moreover have "erase_annotations_adp ` A \<subseteq>
        (P - A) \<union> ((B - A) \<union> erase_annotations_adp ` A)"
      by blast
    ultimately show ?thesis unfolding step_eq
      using adp_step_mono by blast
  qed
qed

theorem relative_adp_com_reduction_pair:
  assumes redpair: "adp_com_redtriple_order S NS NST"
    and all_weak: "\<And>s t. (s,t) \<in> adp_step (P \<union> B) \<Longrightarrow>
      (relative_adp_term_annotation_summary s,
       relative_adp_term_annotation_summary t) \<in> NS"
    and selected_strict: "\<And>s t.
      (s,t) \<in> adp_step_case_rel A True \<Longrightarrow>
      (relative_adp_term_annotation_summary s,
       relative_adp_term_annotation_summary t) \<in> S"
    and residual: "adp_problem_SN
      (P - A, (B - A) \<union> erase_annotations_adp ` A)"
  shows "adp_problem_SN (P,B)"
proof (rule ccontr)
  interpret adp_com_redtriple_order S NS NST by (rule redpair)
  let ?R = "adp_step_case_rel P True"
  let ?W = "adp_step (P \<union> B)"
  let ?D = "adp_step_case_rel A True"
  let ?P' = "P - A"
  let ?B' = "(B - A) \<union> erase_annotations_adp ` A"
  assume not_sn: "\<not> adp_problem_SN (P,B)"
  then obtain terms where deriv: "ideriv ?R ?W terms"
    unfolding adp_problem_SN_def SN_rel_ideriv by auto
  have order_sn: "SN_rel S NS"
    by (rule SN_rel)
  have selected_sn: "SN_rel ?D ?W"
  proof (rule SN_rel_hom[OF order_sn,
      where f=relative_adp_term_annotation_summary])
    fix s t
    assume "(s,t) \<in> ?D"
    then show "(relative_adp_term_annotation_summary s,
        relative_adp_term_annotation_summary t) \<in> S"
      by (rule selected_strict)
  next
    fix s t
    assume "(s,t) \<in> ?W"
    then have "(relative_adp_term_annotation_summary s,
        relative_adp_term_annotation_summary t) \<in> NS"
      by (rule all_weak)
    then show "(relative_adp_term_annotation_summary s,
        relative_adp_term_annotation_summary t) \<in> S \<union> NS" by blast
  qed
  have no_selected:
      "\<not> ideriv (?D \<inter> (?R \<union> ?W))
        ((?R \<union> ?W) - ?D) terms"
  proof
    assume selected: "ideriv (?D \<inter> (?R \<union> ?W))
        ((?R \<union> ?W) - ?D) terms"
    have "ideriv ?D ?W terms"
    proof (rule ideriv_mono[OF _ _ selected])
      show "?D \<inter> (?R \<union> ?W) \<subseteq> ?D" by blast
      show "(?R \<union> ?W) - ?D \<subseteq> ?W"
        using adp_step_case_rel_subset_adp_step[of P True]
          adp_step_mono[of P "P \<union> B"] by blast
    qed
    with selected_sn show False unfolding SN_rel_ideriv by blast
  qed
  from ideriv_split[OF deriv no_selected]
  obtain i where tail: "ideriv (?R - ?D) (?W - ?D) (shift terms i)"
    by blast
  have strict_tail: "?R - ?D \<subseteq> adp_step_case_rel ?P' True"
    by (rule relative_adp_main_without_selected_strict)
  have weak_tail: "?W - ?D \<subseteq> adp_step (?P' \<union> ?B')"
    by (rule relative_adp_steps_without_selected_strict)
  have "ideriv (adp_step_case_rel ?P' True)
      (adp_step (?P' \<union> ?B')) (shift terms i)"
    by (rule ideriv_mono[OF strict_tail weak_tail tail])
  moreover from residual have
      "\<not> (\<exists>xs. ideriv (adp_step_case_rel ?P' True)
        (adp_step (?P' \<union> ?B')) xs)"
    unfolding adp_problem_SN_def SN_rel_ideriv by simp
  ultimately show False by blast
qed
theorem relative_adp_com_reduction_pair_finite_general:
  assumes order: "adp_com_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and lhs_fun: "\<And>pair. pair \<in> P \<union> B \<Longrightarrow> is_Fun (fst pair)"
    and flat_weak: "\<And>pair. pair \<in> P \<union> B \<Longrightarrow>
      relative_adp_com_flat_rule pair \<in> NS"
    and com_weak: "\<And>pair. pair \<in> P \<union> B \<Longrightarrow>
      (relative_adp_com_lhs pair,
       relative_adp_annotation_summary pair) \<in> NS"
    and selected_strict: "\<And>pair. pair \<in> A \<Longrightarrow>
      (relative_adp_com_lhs pair,
       relative_adp_annotation_summary pair) \<in> S"
    and selected: "A \<subseteq> P \<union> B"
    and residual: "adp_problem_SN
      (P - A, (B - A) \<union> erase_annotations_adp ` A)"
  shows "adp_problem_SN (P,B)"
proof (rule relative_adp_com_reduction_pair[OF order])
  fix s t
  assume step: "(s,t) \<in> adp_step (P \<union> B)"
  show "(relative_adp_term_annotation_summary s,
      relative_adp_term_annotation_summary t) \<in> NS"
    by (rule relative_adp_com_all_step_weak[
        OF order invariant discard lhs_fun flat_weak com_weak step])
next
  fix s t
  assume step: "(s,t) \<in> adp_step_case_rel A True"
  show "(relative_adp_term_annotation_summary s,
      relative_adp_term_annotation_summary t) \<in> S"
    by (rule relative_adp_com_selected_step_strict[
        OF order invariant discard lhs_fun flat_weak selected_strict
          selected step])
next
  show "adp_problem_SN (P - A, (B - A) \<union> erase_annotations_adp ` A)"
    by (rule residual)
qed



lemma mono_redtriple_order_imp_adp_com:
  assumes order: "mono_redtriple_order S NS NST"
  shows "adp_com_redtriple_order S NS NST"
proof -
  interpret mono_redtriple_order S NS NST by (rule order)
  have com: "adp_com_monotone S"
    unfolding adp_com_monotone_def
  proof (intro allI impI conjI)
    fix s1 s2 u
    assume rel: "(s1,s2) \<in> S"
    show "(Fun Com2 [s1,u], Fun Com2 [s2,u]) \<in> S"
      using ctxt_closed_one[OF ctxt_S rel, of Com2 "[]" "[u]"] by simp
    show "(Fun Com2 [u,s1], Fun Com2 [u,s2]) \<in> S"
      using ctxt_closed_one[OF ctxt_S rel, of Com2 "[u]" "[]"] by simp
  qed
  show ?thesis
    unfolding adp_com_redtriple_order_def adp_com_redtriple_order_axioms_def
    using mono_redtriple_order.axioms(1)[OF order] com by blast
qed

theorem relative_adp_com_reduction_pair_finite:
  assumes order: "mono_redtriple_order S NS NST"
    and invariant: "adp_com_invariant NS"
    and discard: "adp_com_discarding NS"
    and lhs_fun: "\<And>pair. pair \<in> P \<union> B \<Longrightarrow> is_Fun (fst pair)"
    and flat_weak: "\<And>pair. pair \<in> P \<union> B \<Longrightarrow>
      relative_adp_com_flat_rule pair \<in> NS"
    and com_weak: "\<And>pair. pair \<in> P \<union> B \<Longrightarrow>
      (relative_adp_com_lhs pair,
       relative_adp_annotation_summary pair) \<in> NS"
    and selected_strict: "\<And>pair. pair \<in> A \<Longrightarrow>
      (relative_adp_com_lhs pair,
       relative_adp_annotation_summary pair) \<in> S"
    and selected: "A \<subseteq> P \<union> B"
    and residual: "adp_problem_SN
      (P - A, (B - A) \<union> erase_annotations_adp ` A)"
  shows "adp_problem_SN (P,B)"
  by (rule relative_adp_com_reduction_pair_finite_general[
      OF mono_redtriple_order_imp_adp_com[OF order] invariant discard lhs_fun
      flat_weak com_weak selected_strict selected residual])


end
