theory Sparse_Tiling_Check
  imports Sparse_Tiling_Language
begin

fun sparse_contexts :: "'a list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "sparse_contexts ts p 0 = [[]]"
| "sparse_contexts ts p (Suc n) = concat (map (\<lambda>t.
    if t \<noteq> [] \<and> butlast t = p then
      map (Cons (last t)) (sparse_contexts ts (drop 1 t) n) else []) ts)"

lemma sparse_accept_Cons [simp]:
  "sparse_accept T p (a # w) \<longleftrightarrow>
    p @ [a] \<in> T \<and> sparse_accept T (drop 1 (p @ [a])) w"
  by (simp add: sparse_accept_def)

lemma sparse_accept_append [simp]:
  "sparse_accept T p (u @ v) \<longleftrightarrow>
    sparse_accept T p u \<and> sparse_accept T (sparse_run p u) v"
  by (auto simp: sparse_accept_def sparse_path_append)

lemma sparse_contexts_correct:
  "w \<in> set (sparse_contexts ts p n) \<longleftrightarrow> length w = n \<and> sparse_accept (set ts) p w"
proof (induction n arbitrary: p w)
  case 0
  then show ?case by (auto simp: sparse_accept_def)
next
  case (Suc n)
  show ?case
  proof (cases w)
    case Nil
    then show ?thesis by auto
  next
    case (Cons a v)
    show ?thesis
    proof
      assume member: "w \<in> set (sparse_contexts ts p (Suc n))"
      then obtain t where tile: "t \<in> set ts" and nonempty: "t \<noteq> []"
        and prefix: "butlast t = p" and last: "last t = a"
        and tail: "v \<in> set (sparse_contexts ts (drop 1 t) n)"
        using Cons by auto
      have shape: "t = p @ [a]" using append_butlast_last_id[OF nonempty] by (simp add: prefix last)
      from tail Suc.IH have "length v = n \<and> sparse_accept (set ts) (drop 1 t) v" by blast
      then show "length w = Suc n \<and> sparse_accept (set ts) p w"
        using tile by (simp add: Cons shape)
    next
      assume accepted: "length w = Suc n \<and> sparse_accept (set ts) p w"
      then have tile: "p @ [a] \<in> set ts" and tail: "length v = n \<and> sparse_accept (set ts) (drop 1 (p @ [a])) v"
        by (auto simp: Cons)
      have member: "v \<in> set (sparse_contexts ts (drop 1 (p @ [a])) n)"
        using tail Suc.IH by blast
      show "w \<in> set (sparse_contexts ts p (Suc n))"
        using tile member
        by (fastforce simp: Cons intro: bexI[where x="p @ [a]"])
    qed
  qed
qed

definition sparse_check_tiles where
  "sparse_check_tiles n ts rs ss \<longleftrightarrow>
    list_all (\<lambda>(l,r). l \<noteq> []) rs \<and>
    list_all (\<lambda>p. length p = n \<and>
      list_all (\<lambda>(l,r). list_all (\<lambda>y.
        sparse_accept (set ts) p (l @ y) \<longrightarrow>
        sparse_accept (set ts) p (r @ y) \<and>
        (sparse_path p (l @ y), sparse_path p (r @ y)) \<in> set ss)
        (sparse_contexts ts (sparse_run p l) n)) rs)
      (remdups (map butlast ts))"

lemma sparse_check_tiles_condition:
  assumes checked: "sparse_check_tiles n ts rs ss"
  shows "sparse_tile_condition n (set ts) (set rs) (set ss)"
  unfolding sparse_tile_condition_def
proof (intro allI impI)
  fix p l r y
  assume facts: "length p = n \<and> p \<in> sparse_states (set ts) \<and> (l,r) \<in> set rs \<and>
    length y = n \<and> sparse_accept (set ts) p (l @ y)"
  have state: "p \<in> set (remdups (map butlast ts))"
    using facts by (auto simp: sparse_states_def)
  have context_member: "y \<in> set (sparse_contexts ts (sparse_run p l) n)"
    using facts by (simp add: sparse_contexts_correct)
  show "sparse_accept (set ts) p (r @ y) \<and>
    (sparse_path p (l @ y), sparse_path p (r @ y)) \<in> set ss"
    using checked facts state context_member unfolding sparse_check_tiles_def list_all_iff
    by (simp only: split_beta; blast)
qed

lemma sparse_check_tiles_local_termination:
  assumes checked: "sparse_check_tiles (length q) ts rs ss"
    and border: "length z = length q"
    and target: "SN (sparse_word_step (set ss))"
  shows "SN_on (sparse_word_step (set rs)) {w. sparse_accept (set ts) q (w @ z)}"
proof (rule sparse_local_termination[OF sparse_check_tiles_condition[OF checked] _ border target])
  fix l r
  assume "(l,r) \<in> set rs"
  then show "l \<noteq> []" using checked
    by (auto simp only: sparse_check_tiles_def list_all_iff split: prod.splits)
qed

lemma sparse_check_example:
  "sparse_check_tiles 1 [[0::nat,0]] [([0],[])] [([[0,0],[0,0]],[[0,0]])]"
  by eval

lemma sparse_check_missing_residual:
  "\<not> sparse_check_tiles 1 [[0::nat,0]] [([0],[])] []"
  by eval

lemma sparse_check_empty_left_rejected:
  "\<not> sparse_check_tiles 1 [[0::nat,0]] [([],[0])] []"
  by eval

export_code sparse_check_tiles checking SML

end
