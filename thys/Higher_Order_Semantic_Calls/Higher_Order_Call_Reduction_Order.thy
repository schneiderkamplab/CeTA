theory Higher_Order_Call_Reduction_Order
  imports Higher_Order_Call_Polynomial
begin

lemma ho_arguments_step_pointwise:
  "ho_arguments_step S V R B xs ys \<Longrightarrow>
    list_all2 (\<lambda>x y. x=y \<or> ho_step S V R B x y) xs ys"
proof -
  assume st: "ho_arguments_step S V R B xs ys"
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs" and vw: "ho_step S V R B v w"
    using st unfolding ho_arguments_step_def by blast
  show ?thesis unfolding xs ys by (induction us) (auto simp: list_all2_refl vw)
qed

lemma ho_list_all2_zip_combine:
  assumes p: "list_all2 P As xs" and q: "list_all2 Q xs ys"
    and combine: "\<And>A x y. P A x \<Longrightarrow> Q x y \<Longrightarrow> R A (f x,f y)"
  shows "list_all2 R As (zip (map f xs) (map f ys))"
  using p q
  by (induction arbitrary: ys rule: list_all2_induct) (auto simp: list_all2_Cons1 intro: combine)

theorem ho_call_weight_step:
  assumes zero: "ho_zero_arity_rules R" and closed: "ho_interpretation_closed I"
    and cv: "ho_env_value S I" and mv: "ho_env_value S M" and ev: "ho_env_value (B@V) e"
    and weak: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> ho_weak_rule S I G l r"
    and symbol: "ho_lookup S c=Some A"
    and bound: "n\<le>length (ho_argument_types A)"
    and args: "list_all2 (\<lambda>T x. ho_typeof S V B x=Some T) (take n (ho_argument_types A)) xs"
    and step: "ho_arguments_step S V R B xs ys"
  shows "ho_call_weight S V B I M e c ys\<le>ho_call_weight S V B I M e c xs"
proof -
  let ?eval = "ho_weak_source_interpretation S V B I e"
  have pair: "ho_value T (?eval x) \<and> ho_value T (?eval y) \<and> ho_value_ge T (?eval x) (?eval y)"
    if ty: "ho_typeof S V B x=Some T" and xy: "x=y \<or> ho_step S V R B x y" for T x y
  proof -
    have xv: "ho_value T (?eval x)" by (rule ho_weak_source_interpretation_value[OF ty closed cv ev])
    show ?thesis
    proof (cases "x=y")
      case True
      then show ?thesis using xv ho_value_ge_refl[OF xv] by simp
    next
      case False
      have st: "ho_step S V R B x y" using xy False by blast
      have yt: "ho_typeof S V B y=Some T" by (rule ho_zero_arity_step_type[OF st zero ty])
      have yv: "ho_value T (?eval y)" by (rule ho_weak_source_interpretation_value[OF yt closed cv ev])
      have ge: "ho_value_ge T (?eval x) (?eval y)" by (rule ho_weak_source_step_ge[OF st zero closed cv weak ty ev])
      show ?thesis using xv yv ge by simp
    qed
  qed
  have triples: "list_all2 (\<lambda>T (x,y). ho_value T x \<and> ho_value T y \<and> ho_value_ge T x y)
      (take n (ho_argument_types A)) (zip (map ?eval xs) (map ?eval ys))"
    by (rule ho_list_all2_zip_combine[OF args ho_arguments_step_pointwise[OF step]]) (simp add: pair)
  have len: "length xs=length ys" using ho_arguments_step_pointwise[OF step] list_all2_lengthD by blast
  have ge: "ho_call_arguments_ge A (map ?eval xs) (map ?eval ys)"
    using ho_call_arguments_geI[OF bound triples] len by (simp add: map_fst_zip map_snd_zip)
  have mc: "ho_value A (M c)" using mv symbol by (auto simp: ho_env_value_def split: if_splits)
  have order: "ho_value_ge (ho_drop_type (length xs) A) (foldl App (M c) (map ?eval xs)) (foldl App (M c) (map ?eval ys))"
    using ho_fold_call_ge[OF ge mc mc ho_value_ge_refl[OF mc]] by simp
  show ?thesis using ho_value_ge_observe[OF order] symbol len
    by (auto simp: ho_call_weight_def ho_call_value_def split: if_splits)
qed

end
