theory Higher_Order_Call_Comparison
  imports Higher_Order_Call_Reduction_Order
begin

definition ho_check_call_comparison where
  "ho_check_call_comparison S ps ms fuel G c ls d xs strict =
    (c<length S \<and> d<length S \<and>
      length ls\<le>length (ho_argument_types (S!c)) \<and>
      length xs\<le>length (ho_argument_types (S!d)) \<and>
      list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (length ls) (ho_argument_types (S!c))) ls \<and>
      list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (length xs) (ho_argument_types (S!d))) xs \<and>
      ho_drop_type (length ls) (S!c)=ho_drop_type (length xs) (S!d) \<and>
      (if strict then ho_check_polynomial_gt else ho_check_polynomial_ge) fuel G
        (ho_drop_type (length ls) (S!c)) (ho_call_polynomial S ps ms G c ls) (ho_call_polynomial S ps ms G d xs))"

lemma ho_typed_arguments_exist:
  "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) As xs \<Longrightarrow>
    x\<in>set xs \<Longrightarrow> \<exists>A. ho_typeof S G [] x=Some A"
  by (induction rule: list_all2_induct) auto

lemma ho_typed_arguments_open:
  "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) As xs \<Longrightarrow>
    map (ho_open s b 0) xs=map (ho_subst s 0) xs"
  by (induction rule: list_all2_induct) (auto intro!: ho_open_closed dest: ho_typeof_bound_closed)

theorem ho_check_call_comparison_sound:
  assumes ps: "ho_check_polynomial_signature S ps" and ms: "ho_check_polynomial_signature S ms"
    and check: "ho_check_call_comparison S ps ms fuel G c ls d xs strict"
    and subst: "ho_typed_subst S V B G s" and ev: "ho_env_value (B@V) e"
  defines "I \<equiv> ho_polynomial_interpretation ps" and "M \<equiv> ho_polynomial_interpretation ms"
  shows "if strict then
      ho_call_weight S V B I M e d (map (ho_open s b 0) xs) < ho_call_weight S V B I M e c (map (ho_subst s 0) ls)
    else ho_call_weight S V B I M e d (map (ho_open s b 0) xs) \<le> ho_call_weight S V B I M e c (map (ho_subst s 0) ls)"
proof -
  let ?A = "ho_drop_type (length ls) (S!c)"
  let ?env = "\<lambda>n. ho_weak_source_interpretation S V B I e (s n)"
  have ci: "c<length S" and di: "d<length S"
    and cb: "length ls\<le>length (ho_argument_types (S!c))"
    and db: "length xs\<le>length (ho_argument_types (S!d))"
    and lt: "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (length ls) (ho_argument_types (S!c))) ls"
    and xt: "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (length xs) (ho_argument_types (S!d))) xs"
    and eq: "?A=ho_drop_type (length xs) (S!d)"
    and ck: "(if strict then ho_check_polynomial_gt else ho_check_polynomial_ge) fuel G ?A
      (ho_call_polynomial S ps ms G c ls) (ho_call_polynomial S ps ms G d xs)"
    using check by (auto simp: ho_check_call_comparison_def)
  have closed: "ho_interpretation_closed I" unfolding I_def by (rule ho_polynomial_signature_closed[OF ps])
  have iv: "ho_env_value S I" unfolding I_def by (rule ho_polynomial_signature_value[OF ps])
  have env: "ho_env_value G ?env" by (rule ho_weak_source_instance_env[OF subst closed iv ev])
  have lv: "ho_polynomial_eval ?env (ho_call_polynomial S ps ms G c ls) =
      ho_call_value S V B I M e c (map (ho_subst s 0) ls)"
    using ho_call_polynomial_eval[where e="?env" and G=G, OF ps ms ci cb]
      ho_call_value_instance[where M=M and e=e and c=c and xs=ls, OF ho_typed_arguments_exist[OF lt] subst closed]
    by (simp add: I_def M_def)
  have xv: "ho_polynomial_eval ?env (ho_call_polynomial S ps ms G d xs) =
      ho_call_value S V B I M e d (map (ho_open s b 0) xs)"
    using ho_call_polynomial_eval[where e="?env" and G=G, OF ps ms di db]
      ho_call_value_instance[where M=M and e=e and c=d and xs=xs, OF ho_typed_arguments_exist[OF xt] subst closed]
    by (simp add: I_def M_def ho_typed_arguments_open[OF xt, of s b])
  show ?thesis
  proof (cases strict)
    case True
    have order: "ho_value_gt ?A (ho_polynomial_eval ?env (ho_call_polynomial S ps ms G c ls))
        (ho_polynomial_eval ?env (ho_call_polynomial S ps ms G d xs))"
      by (rule ho_check_polynomial_gt_sound[OF _ env]) (use ck True in simp)
    show ?thesis using ho_value_gt_observe[OF order] eq
      by (simp add: True lv xv ho_call_weight_def)
  next
    case False
    have order: "ho_value_ge ?A (ho_polynomial_eval ?env (ho_call_polynomial S ps ms G c ls))
        (ho_polynomial_eval ?env (ho_call_polynomial S ps ms G d xs))"
      by (rule ho_check_polynomial_ge_sound[OF _ env]) (use ck False in simp)
    show ?thesis using ho_value_ge_observe[OF order] eq
      by (simp add: False lv xv ho_call_weight_def)
  qed
qed

end
