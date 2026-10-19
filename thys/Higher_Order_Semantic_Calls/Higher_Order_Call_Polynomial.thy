theory Higher_Order_Call_Polynomial
  imports Higher_Order_Call_Values
begin

fun ho_polynomial_apply_list where
  "ho_polynomial_apply_list A p []=p"
| "ho_polynomial_apply_list (HArrow A C) p (q#qs)=ho_polynomial_apply_list C (HPApply A C p q) qs"
| "ho_polynomial_apply_list (HBase b) p (q#qs)=HPNumber b 0"

lemma ho_polynomial_apply_list_eval:
  "length qs\<le>length (ho_argument_types A) \<Longrightarrow>
    ho_polynomial_eval e (ho_polynomial_apply_list A p qs) =
      foldl App (ho_polynomial_eval e p) (map (ho_polynomial_eval e) qs)"
proof (induction qs arbitrary: A p)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  obtain T C where a: "A=HArrow T C" using Cons.prems by (cases A) auto
  have bound: "length qs\<le>length (ho_argument_types C)" using Cons.prems a by simp
  show ?case using Cons.IH[where p="HPApply T C p q", OF bound] by (simp add: a)
qed

definition ho_call_polynomial where
  "ho_call_polynomial S ps ms G c xs = ho_polynomial_apply_list (S!c) (ms!c)
    (map (\<lambda>x. ho_weak_polynomial_translate ps (ho_compile S G [] x)) xs)"

lemma ho_call_polynomial_eval:
  assumes ps: "ho_check_polynomial_signature S ps" and ms: "ho_check_polynomial_signature S ms"
    and c: "c<length S" and bound: "length xs\<le>length (ho_argument_types (S!c))"
  shows "ho_polynomial_eval e (ho_call_polynomial S ps ms G c xs) =
    ho_call_value S G [] (ho_polynomial_interpretation ps) (ho_polynomial_interpretation ms) e c xs"
proof -
  have cm: "c<length ms" and mty: "ho_polynomial_typeof [] (ms!c)=Some (S!c)"
    using ms c by (auto simp: ho_check_polynomial_signature_iff)
  have eq: "ho_polynomial_eval e (ms!c)=ho_polynomial_eval Var (ms!c)"
    by (rule ho_polynomial_eval_cong[OF ho_polynomial_typeof_sound[OF mty]]) simp
  show ?thesis unfolding ho_call_polynomial_def ho_call_value_def
    by (subst ho_polynomial_apply_list_eval)
      (use bound in simp, simp add: eq ho_polynomial_interpretation_def cm map_map
        ho_weak_polynomial_translate_eval[OF ps] ho_weak_source_interpretation_def[abs_def] o_def)
qed

definition ho_check_weak_polynomial_rule where
  "ho_check_weak_polynomial_rule S ps fuel G l r =
    (case ho_typeof S G [] (ho_erase_pattern l) of None \<Rightarrow> False | Some A \<Rightarrow>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      ho_check_polynomial_ge fuel G A
        (ho_weak_polynomial_translate ps (ho_compile S G [] (ho_erase_pattern l)))
        (ho_weak_polynomial_translate ps (ho_compile S G [] (ho_erase_pattern r))))"

lemma ho_check_weak_polynomial_rule_sound:
  assumes signature: "ho_check_polynomial_signature S ps"
    and check: "ho_check_weak_polynomial_rule S ps fuel G l r"
  shows "ho_weak_rule S (ho_polynomial_interpretation ps) G l r"
proof -
  obtain A where l: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    and order: "ho_check_polynomial_ge fuel G A
      (ho_weak_polynomial_translate ps (ho_compile S G [] (ho_erase_pattern l)))
      (ho_weak_polynomial_translate ps (ho_compile S G [] (ho_erase_pattern r)))"
    using check by (auto simp: ho_check_weak_polynomial_rule_def split: option.splits)
  have ge: "ho_value_ge A (ho_weak_source_interpretation S G [] (ho_polynomial_interpretation ps) e (ho_erase_pattern l))
      (ho_weak_source_interpretation S G [] (ho_polynomial_interpretation ps) e (ho_erase_pattern r))"
    if "ho_env_value G e" for e
    using ho_check_polynomial_ge_sound[OF order that]
    by (simp add: ho_weak_source_interpretation_def ho_weak_polynomial_translate_eval[OF signature])
  show ?thesis unfolding ho_weak_rule_def using l r ge by blast
qed

end
