theory Higher_Order_Call_Values
  imports Higher_Order_Weak_Polynomial
begin

lemma ho_weak_source_instance_eq:
  assumes ty: "ho_typeof S G [] t=Some A" and subst: "ho_typed_subst S V B G s"
    and closed: "ho_interpretation_closed I"
  shows "ho_weak_source_interpretation S V B I e (ho_subst s 0 t) =
    ho_weak_source_interpretation S G [] I (\<lambda>n. ho_weak_source_interpretation S V B I e (s n)) t"
  unfolding ho_weak_source_interpretation_def ho_compile_free_subst[OF ty subst]
  by (rule ho_weak_evaluate_expr_subst[OF closed])

lemma ho_weak_source_instance_env:
  assumes subst: "ho_typed_subst S V B G s" and closed: "ho_interpretation_closed I"
    and cv: "ho_env_value S I" and ev: "ho_env_value (B@V) e"
  shows "ho_env_value G (\<lambda>n. ho_weak_source_interpretation S V B I e (s n))"
  unfolding ho_env_value_def
proof (intro allI impI)
  fix n assume n: "n<length G"
  have ty: "ho_typeof S V B (s n)=Some (G!n)" using subst n by (simp add: ho_typed_subst_def)
  show "ho_value (G!n) (ho_weak_source_interpretation S V B I e (s n))"
    by (rule ho_weak_source_interpretation_value[OF ty closed cv ev])
qed

definition ho_call_value where
  "ho_call_value S V B I M e c xs = foldl App (M c) (map (ho_weak_source_interpretation S V B I e) xs)"

definition ho_call_weight where
  "ho_call_weight S V B I M e c xs = ho_observe (ho_drop_type (length xs) (S!c))
    (ho_call_value S V B I M e c xs)"

lemma ho_call_value_instance:
  assumes types: "\<And>x. x\<in>set xs \<Longrightarrow> \<exists>A. ho_typeof S G [] x=Some A"
    and subst: "ho_typed_subst S V B G s" and closed: "ho_interpretation_closed I"
  shows "ho_call_value S V B I M e c (map (ho_subst s 0) xs) =
    ho_call_value S G [] I M (\<lambda>n. ho_weak_source_interpretation S V B I e (s n)) c xs"
proof -
  have each: "ho_weak_source_interpretation S V B I e (ho_subst s 0 x) =
      ho_weak_source_interpretation S G [] I (\<lambda>n. ho_weak_source_interpretation S V B I e (s n)) x"
    if "x\<in>set xs" for x
  proof -
    note member = that
    obtain A where ty: "ho_typeof S G [] x=Some A" using types[OF member] by blast
    show ?thesis by (rule ho_weak_source_instance_eq[OF ty subst closed])
  qed
  show ?thesis unfolding ho_call_value_def by (simp add: map_map each cong: map_cong)
qed

fun ho_call_arguments_ge where
  "ho_call_arguments_ge A [] [] = True"
| "ho_call_arguments_ge (HArrow A C) (x#xs) (y#ys) =
    (ho_value A x \<and> ho_value A y \<and> ho_value_ge A x y \<and> ho_call_arguments_ge C xs ys)"
| "ho_call_arguments_ge A xs ys = False"

lemma ho_call_arguments_ge_length:
  "ho_call_arguments_ge A xs ys \<Longrightarrow> length xs=length ys"
  by (induction A xs ys rule: ho_call_arguments_ge.induct) auto

lemma ho_fold_call_ge:
  assumes args: "ho_call_arguments_ge A xs ys"
    and f: "ho_value A f" and g: "ho_value A g" and fg: "ho_value_ge A f g"
  shows "ho_value (ho_drop_type (length xs) A) (foldl App f xs) \<and>
    ho_value (ho_drop_type (length xs) A) (foldl App g ys) \<and>
    ho_value_ge (ho_drop_type (length xs) A) (foldl App f xs) (foldl App g ys)"
  using args f g fg
proof (induction A xs ys arbitrary: f g rule: ho_call_arguments_ge.induct)
  case (2 A C x xs y ys)
  have fv: "ho_value C (App f x)" and gv: "ho_value C (App g y)" using "2.prems" by auto
  have ge: "ho_value_ge C (App f x) (App g y)"
    using ho_plain_app_ge[where A=A and B=C and f=f and g=g and x=x and y=y] "2.prems"
    by (simp add: ho_plain_app_def)
  show ?case using "2.IH"[OF _ fv gv ge] "2.prems"(1) by simp
qed auto

lemma ho_call_arguments_geI:
  assumes bound: "n\<le>length (ho_argument_types A)"
    and args: "list_all2 (\<lambda>T (x,y). ho_value T x \<and> ho_value T y \<and> ho_value_ge T x y)
      (take n (ho_argument_types A)) zs"
  shows "ho_call_arguments_ge A (map fst zs) (map snd zs)"
  using bound args
proof (induction n arbitrary: A zs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain T C where a: "A=HArrow T C" using Suc.prems(1) by (cases A) auto
  obtain x y rest where zs: "zs=(x,y)#rest"
    and first: "ho_value T x \<and> ho_value T y \<and> ho_value_ge T x y"
    and tail: "list_all2 (\<lambda>T (x,y). ho_value T x \<and> ho_value T y \<and> ho_value_ge T x y)
      (take n (ho_argument_types C)) rest"
    using Suc.prems(2) a by (auto simp: list_all2_Cons1)
  have n: "n\<le>length (ho_argument_types C)" using Suc.prems(1) a by simp
  show ?case using Suc.IH[OF n tail] first by (simp add: a zs)
qed

end
