theory Rule_Bucket_Performance
  imports "Proof_Checker.CPF_Parser"
begin

text \<open>Keep the exact list order and RBT representation, while sharing
membership indexes across an entire insertion batch.\<close>
definition bucket_index_valid where
  "bucket_index_valid m ix \<longleftrightarrow> (\<forall>k. RBT.lookup ix k = map_option set (RBT.lookup m k))"

definition indexed_insert_step where
  "indexed_insert_step key_of v accum = (case accum of (m,ix) \<Rightarrow>
    (case key_of v of None \<Rightarrow> (m,ix) | Some k \<Rightarrow>
      (case RBT.lookup m k of None \<Rightarrow> (RBT.insert k [v] m, RBT.insert k {v} ix)
      | Some xs \<Rightarrow> (let S = the (RBT.lookup ix k) in
          (RBT.insert k (if v \<in> S then xs else v#xs) m,
           RBT.insert k (insert v S) ix)))))"

lemma indexed_insert_step_correct:
  assumes "bucket_index_valid m ix"
  shows "fst (indexed_insert_step key_of v (m,ix)) = insert_value key_of v m"
    and "bucket_index_valid (fst (indexed_insert_step key_of v (m,ix)))
        (snd (indexed_insert_step key_of v (m,ix)))"
  using assms
  by (auto simp: indexed_insert_step_def bucket_index_valid_def insert_value_def Let_def
      List.insert_def fun_eq_iff split: option.splits)

lemma indexed_insert_step_pair:
  assumes "bucket_index_valid (fst accum) (snd accum)"
  shows "fst (indexed_insert_step key_of v accum) = insert_value key_of v (fst accum)"
    and "bucket_index_valid (fst (indexed_insert_step key_of v accum)) (snd (indexed_insert_step key_of v accum))"
  using indexed_insert_step_correct[OF assms, of key_of v] by simp_all

fun indexed_insert_values where
  "indexed_insert_values key_of [] accum = accum"
| "indexed_insert_values key_of (v#vs) accum = indexed_insert_step key_of v (indexed_insert_values key_of vs accum)"

lemma indexed_insert_values_invariant:
  assumes "bucket_index_valid m ix"
  shows "fst (indexed_insert_values key_of vs (m,ix)) = insert_values key_of vs m \<and>
     bucket_index_valid (fst (indexed_insert_values key_of vs (m,ix)))
        (snd (indexed_insert_values key_of vs (m,ix)))"
proof (induction vs)
  case Nil
  then show ?case using assms by simp
next
  case (Cons v vs)
  let ?a = "indexed_insert_values key_of vs (m,ix)"
  have inv: "bucket_index_valid (fst ?a) (snd ?a)" using Cons.IH by blast
  have eq: "fst ?a = insert_values key_of vs m" using Cons.IH by blast
  from indexed_insert_step_pair[OF inv, of key_of v] eq
  show ?case by simp
qed

lemma indexed_insert_values_correct:
  assumes "bucket_index_valid m ix"
  shows "fst (indexed_insert_values key_of vs (m,ix)) = insert_values key_of vs m"
    and "bucket_index_valid (fst (indexed_insert_values key_of vs (m,ix)))
        (snd (indexed_insert_values key_of vs (m,ix)))"
  using indexed_insert_values_invariant[OF assms, of key_of vs] by blast+

declare insert_values.simps[code del]
lemma insert_values_indexed_code [code]:
  "insert_values key_of vs m = fst (indexed_insert_values key_of vs (m, RBT.map (\<lambda>k xs. set xs) m))"
  using indexed_insert_values_correct(1)[of m "RBT.map (\<lambda>k xs. set xs) m" key_of vs]
  by (simp add: bucket_index_valid_def)

lemma rb_map_balance:
  "RBT_Impl.map f (balance l k v r) = balance (RBT_Impl.map f l) k (f k v) (RBT_Impl.map f r)"
  by (induction l k v r rule: balance.induct) simp_all
lemma rb_map_paint:
  "RBT_Impl.map f (paint c t) = paint c (RBT_Impl.map f t)"
  by (cases t) simp_all
lemma rb_map_insert:
  fixes k :: "'a::linorder"
  shows
  "RBT_Impl.map f (rbt_ins (\<lambda>_ _ nv. nv) k v t) =
    rbt_ins (\<lambda>_ _ nv. nv) k (f k v) (RBT_Impl.map f t)"
proof (induction t)
  case Empty
  then show ?case by simp
next
  case (Branch c l x y r)
  then show ?case by (cases c) (auto simp: rb_map_balance)
qed
lemma bucket_map_insert:
  "RBT.map f (RBT.insert k v t) = RBT.insert k (f k v) (RBT.map f t)"
  by (rule RBT.rbt_eqI)
    (simp add: RBT.map.rep_eq RBT.insert.rep_eq rbt_insert_def rbt_insert_with_key_def rb_map_paint rb_map_insert)
lemma rb_map_identity:
  "(\<And>k v. (k,v) \<in> set (RBT_Impl.entries t) \<Longrightarrow> f k v = v) \<Longrightarrow> RBT_Impl.map f t = t"
  by (induction t) auto
lemma bucket_map_identity:
  assumes "\<And>k v. (k,v) \<in> set (RBT.entries t) \<Longrightarrow> f k v = v"
  shows "RBT.map f t = t"
  apply (rule RBT.rbt_eqI)
  apply (simp only: RBT.map.rep_eq)
  apply (rule rb_map_identity)
  using assms by (simp add: RBT.entries.rep_eq)
lemma rb_map_comp:
  "RBT_Impl.map f (RBT_Impl.map g t) = RBT_Impl.map (\<lambda>k v. f k (g k v)) t"
  by (induction t) auto
lemma bucket_map_comp:
  "RBT.map f (RBT.map g t) = RBT.map (\<lambda>k v. f k (g k v)) t"
  by (rule RBT.rbt_eqI) (simp add: RBT.map.rep_eq rb_map_comp)


text \<open>Filter each bucket once for a deletion batch. Replaying just the
key updates preserves even the original tree shape and colors; it never scans
the surviving value lists again.\<close>
definition bucket_filter where
  "bucket_filter key_of D m = RBT.map (\<lambda>k xs. filter (\<lambda>v. key_of v \<noteq> Some k \<or> v \<notin> D) xs) m"
definition bucket_clean where
  "bucket_clean key_of D m \<longleftrightarrow> (\<forall>k xs v. RBT.lookup m k = Some xs \<longrightarrow>
     v \<in> set xs \<longrightarrow> key_of v = Some k \<longrightarrow> v \<notin> D)"

lemma filter_removeAll_commute:
  "filter P (removeAll v xs) = removeAll v (filter P xs)"
  by (induction xs) auto
lemma bucket_filter_delete_value:
  "bucket_filter key_of D (delete_value key_of v m) = delete_value key_of v (bucket_filter key_of D m)"
  by (auto simp: bucket_filter_def delete_value_def bucket_map_insert
      filter_removeAll_commute split: option.splits)
lemma bucket_filter_delete_values:
  "bucket_filter key_of D (delete_values key_of vs m) = delete_values key_of vs (bucket_filter key_of D m)"
  by (induction vs) (simp_all add: bucket_filter_delete_value)
lemma bucket_clean_filtered:
  "bucket_clean key_of D (bucket_filter key_of D m)"
  by (auto simp: bucket_clean_def bucket_filter_def split: option.splits)
lemma bucket_filter_fixed:
  assumes "bucket_clean key_of D m"
  shows "bucket_filter key_of D m = m"
  unfolding bucket_filter_def
  apply (rule bucket_map_identity)
  using assms by (auto simp: bucket_clean_def RBT.lookup_in_tree filter_id_conv)
lemma bucket_clean_delete_value:
  assumes "bucket_clean key_of D m"
  shows "bucket_clean key_of (insert v D) (delete_value key_of v m)"
  using assms by (auto simp: bucket_clean_def delete_value_def split: option.splits if_splits)
lemma bucket_clean_delete_values:
  assumes "bucket_clean key_of D m"
  shows "bucket_clean key_of (D \<union> set vs) (delete_values key_of vs m)"
proof (induction vs)
  case Nil
  then show ?case using assms by simp
next
  case (Cons v vs)
  have "bucket_clean key_of (insert v (D \<union> set vs)) (delete_value key_of v (delete_values key_of vs m))"
    by (rule bucket_clean_delete_value[OF Cons.IH])
  then show ?case by (simp add: Un_insert_right)
qed

definition touch_bucket where
  "touch_bucket key_of v m = (case key_of v of None \<Rightarrow> m | Some k \<Rightarrow>
    (case RBT.lookup m k of None \<Rightarrow> m | Some xs \<Rightarrow> RBT.insert k xs m))"
fun touch_buckets where
  "touch_buckets key_of [] m = m"
| "touch_buckets key_of (v#vs) m = touch_bucket key_of v (touch_buckets key_of vs m)"
lemma touch_bucket_clean:
  "bucket_clean key_of D m \<Longrightarrow> bucket_clean key_of D (touch_bucket key_of v m)"
  by (auto simp: bucket_clean_def touch_bucket_def split: option.splits if_splits)
lemma touch_buckets_clean:
  "bucket_clean key_of D m \<Longrightarrow> bucket_clean key_of D (touch_buckets key_of vs m)"
  by (induction vs) (simp_all add: touch_bucket_clean)
lemma delete_clean_touch:
  assumes "bucket_clean key_of D m" "v \<in> D"
  shows "delete_value key_of v m = touch_bucket key_of v m"
  using assms by (auto simp: bucket_clean_def delete_value_def touch_bucket_def split: option.splits; metis removeAll_id)
lemma delete_values_clean_touch:
  assumes "bucket_clean key_of D m" "set vs \<subseteq> D"
  shows "delete_values key_of vs m = touch_buckets key_of vs m"
  using assms
proof (induction vs)
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  have sub: "set vs \<subseteq> D" and mem: "v \<in> D" using Cons.prems by auto
  have ih: "delete_values key_of vs m = touch_buckets key_of vs m"
    by (rule Cons.IH[OF Cons.prems(1) sub])
  have cl: "bucket_clean key_of D (touch_buckets key_of vs m)"
    by (rule touch_buckets_clean[OF Cons.prems(1)])
  have eq: "delete_value key_of v (touch_buckets key_of vs m) = touch_bucket key_of v (touch_buckets key_of vs m)"
    by (rule delete_clean_touch[OF cl mem])
  show ?case by (simp add: ih eq)
qed

declare delete_values.simps[code del]
lemma delete_values_batched_code [code]:
  "delete_values key_of vs m = touch_buckets key_of vs (bucket_filter key_of (set vs) m)"
proof -
  have clean: "bucket_clean key_of (set vs) (delete_values key_of vs m)"
    using bucket_clean_delete_values[of key_of "{}" m vs] by (simp add: bucket_clean_def)
  have "delete_values key_of vs m = bucket_filter key_of (set vs) (delete_values key_of vs m)"
    using bucket_filter_fixed[OF clean] by simp
  also have "... = delete_values key_of vs (bucket_filter key_of (set vs) m)"
    by (rule bucket_filter_delete_values)
  also have "... = touch_buckets key_of vs (bucket_filter key_of (set vs) m)"
    by (rule delete_values_clean_touch[OF bucket_clean_filtered]) simp
  finally show ?thesis .
qed

end
