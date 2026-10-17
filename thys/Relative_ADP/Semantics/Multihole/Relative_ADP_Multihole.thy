theory Relative_ADP_Multihole
  imports
    Relative_ADP_Root_Case_Dev.Relative_ADP_Root_Case
    First_Order_Rewriting.Multihole_Context
    CR.LS_Basics
begin

text \<open>
  This leaf isolates the multihole-context infrastructure used in the hard
  root-base case of the relative ADP chain criterion.  The initial context
  retains only the root of a term; its immediate arguments are the carriers
  from the proof of Theorem 23.
\<close>

fun root_hole_mctxt :: "('f, 'v) term \<Rightarrow> ('f, 'v) mctxt" where
  "root_hole_mctxt (Var x) = MVar x"
| "root_hole_mctxt (Fun f ts) = MFun f (replicate (length ts) MHole)"

fun root_hole_terms :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list" where
  "root_hole_terms (Var x) = []"
| "root_hole_terms (Fun f ts) = ts"

lemma root_hole_num_holes:
  "num_holes (root_hole_mctxt t) = length (root_hole_terms t)"
  by (cases t) simp_all

lemma root_hole_fill:
  "fill_holes (root_hole_mctxt t) (root_hole_terms t) = t"
proof (cases t)
  case (Var x)
  then show ?thesis by simp
next
  case (Fun f ts)
  have sum_replicate_one: "sum_list (replicate n (Suc 0)) = n" for n
    by (induct n) simp_all
  have part: "partition_holes ts (replicate (length ts) MHole) = map (\<lambda>t. [t]) ts"
  proof (rule nth_equalityI)
    show "length (partition_holes ts (replicate (length ts) MHole)) =
        length (map (\<lambda>t. [t]) ts)"
      by simp
    fix i
    assume i: "i < length (partition_holes ts (replicate (length ts) MHole))"
    have i_ts: "i < length ts" using i by simp
    have drop_i: "drop i ts = ts ! i # drop (Suc i) ts"
      using i_ts
    proof (induct ts arbitrary: i)
      case Nil
      then show ?case by simp
    next
      case (Cons t ts)
      then show ?case by (cases i) simp_all
    qed
    then show "partition_holes ts (replicate (length ts) MHole) ! i =
        map (\<lambda>t. [t]) ts ! i"
      using partition_by_nth[of i "replicate (length ts) 1" ts]
      by (simp add: sum_replicate_one drop_i i_ts)
  qed
  show ?thesis unfolding Fun
    apply (simp only: root_hole_mctxt.simps root_hole_terms.simps
        fill_holes.simps)
    apply (subst part)
    apply (auto simp: nth_replicate intro!: nth_equalityI)
    done
qed

lemma root_in_root_hole_poss:
  assumes "is_Fun t"
  shows "[] \<in> poss_mctxt (root_hole_mctxt t)"
  using assms by (cases t) simp_all

lemma root_hole_context_positions:
  assumes "is_Fun t"
  shows "poss_mctxt (root_hole_mctxt t) = {[]}"
  using assms by (cases t) (auto simp: nth_replicate)

text \<open>
  A rewrite of a filled context is either at a function position retained by
  the context or strictly inside one uniquely indexed hole.  This local copy
  avoids importing the substantially larger layer-systems development.
\<close>

lemmas relative_adp_filled_rewrite_cases = rewrite_cases

end
