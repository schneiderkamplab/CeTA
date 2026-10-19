theory Higher_Order_Meta_Polynomial
  imports Higher_Order_Meta_Order
begin

fun ho_meta_polynomial_spine where
  "ho_meta_polynomial_spine T p []=p"
| "ho_meta_polynomial_spine T p (q#qs)=(case T of HArrow A C \<Rightarrow>
    ho_meta_polynomial_spine C (HPApply A C p q) qs | _ \<Rightarrow> HPNumber 0 0)"

fun ho_meta_polynomial where
  "ho_meta_polynomial S G D ps (PBound n)=HPVar n"
| "ho_meta_polynomial S G D ps (PConst n)=(if n<length ps then ps!n else HPNumber 0 0)"
| "ho_meta_polynomial S G D ps (PApp p q)=(case ho_typeof S G D (ho_erase_pattern p) of
    Some (HArrow A C) \<Rightarrow>
      ho_polynomial_raise C (HPApply A C (ho_meta_polynomial S G D ps p) (ho_meta_polynomial S G D ps q))
        (ho_polynomial_lower A (ho_meta_polynomial S G D ps q)) | _ \<Rightarrow> HPNumber 0 0)"
| "ho_meta_polynomial S G D ps (PAbs A p)=(case ho_typeof S G (A#D) (ho_erase_pattern p) of
    Some C \<Rightarrow> HPAbstract A C (ho_meta_polynomial S G (A#D) ps p) | _ \<Rightarrow> HPNumber 0 0)"
| "ho_meta_polynomial S G D ps (PMeta n qs)=(case ho_lookup G n of Some T \<Rightarrow>
    ho_meta_polynomial_spine T (HPVar (length D+n)) (map (ho_meta_polynomial S G D ps) qs)
    | _ \<Rightarrow> HPNumber 0 0)"

lemma ho_meta_polynomial_spine_eval:
  assumes typed: "ho_typeof S G D (foldl HApp t ts)=Some A"
    and len: "length qs=length ts" and head: "ho_typeof S G D t=Some T"
  shows "ho_polynomial_eval e (ho_meta_polynomial_spine T p qs)=
    foldl App (ho_polynomial_eval e p) (map (ho_polynomial_eval e) qs)"
using typed len head
proof (induction ts arbitrary: t T p qs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain q rest where qs: "qs=q#rest" and len: "length rest=length xs"
    using Cons.prems(2) by (cases qs) auto
  have typed: "ho_typeof S G D (foldl HApp (HApp t x) xs)=Some A" using Cons.prems(1) by simp
  obtain C where app: "ho_typeof S G D (HApp t x)=Some C"
    using ho_typed_fold_head[OF typed] by blast
  obtain U where ty: "T=HArrow U C" using app Cons.prems(3)
    by (auto split: option.splits ho_type.splits if_splits)
  show ?case using Cons.IH[OF typed len app, of "HPApply U C p q"] by (simp add: qs ty)
qed

lemma ho_meta_polynomial_eval:
  assumes typed: "ho_typeof S G D (ho_erase_pattern p)=Some A"
    and signature: "ho_check_polynomial_signature S ps"
  shows "ho_polynomial_eval e (ho_meta_polynomial S G D ps p)=
    ho_pattern_interpretation S G D (ho_polynomial_interpretation ps) (\<lambda>n. e (length D+n)) e p"
using typed
proof (induction p arbitrary: D A e)
  case (PBound n)
  then show ?case by simp
next
  case (PConst n)
  have n: "n<length S" using PConst.prems by (auto split: if_splits)
  have np: "n<length ps" and ty: "ho_polynomial_type [] (ps!n) (S!n)"
    using signature n ho_polynomial_typeof_sound by (auto simp: ho_check_polynomial_signature_iff)
  have eq: "ho_polynomial_eval e (ps!n)=ho_polynomial_eval Var (ps!n)"
    by (rule ho_polynomial_eval_cong[OF ty]) simp
  show ?case by (simp add: np eq ho_polynomial_interpretation_def)
next
  case (PApp p q)
  obtain T where p: "ho_typeof S G D (ho_erase_pattern p)=Some (HArrow T A)"
    and q: "ho_typeof S G D (ho_erase_pattern q)=Some T"
    using PApp.prems by (auto split: option.splits ho_type.splits if_splits)
  show ?case by (simp add: p PApp.IH(1)[OF p] PApp.IH(2)[OF q]
    ho_polynomial_raise_eval ho_polynomial_lower_eval ho_sem_app_def)
next
  case (PAbs T p)
  obtain C where p: "ho_typeof S G (T#D) (ho_erase_pattern p)=Some C"
    using PAbs.prems by (auto split: option.splits)
  have env: "(\<lambda>n. ho_env_lift e (length (T#D)+n))=(\<lambda>n. lift (e (length D+n)) 0)"
    by (rule ext) (simp add: ho_env_lift_def ho_env_cons_def)
  show ?case using PAbs.IH[OF p, of "ho_env_lift e"]
    by (simp only: ho_meta_polynomial.simps p option.simps ho_polynomial_eval.simps
      ho_pattern_interpretation.simps env)
next
  case (PMeta n qs)
  have typed: "ho_typeof S G D (foldl HApp (HFree n) (map ho_erase_pattern qs))=Some A"
    using PMeta.prems by simp
  obtain T where head: "ho_typeof S G D (HFree n)=Some T" using ho_typed_fold_head[OF typed] by blast
  have types: "\<And>q. q\<in>set qs \<Longrightarrow> \<exists>T. ho_typeof S G D (ho_erase_pattern q)=Some T"
    using ho_typed_fold_arguments[OF typed] by (simp add: list_all_iff)
  have args: "map (\<lambda>q. ho_polynomial_eval e (ho_meta_polynomial S G D ps q)) qs =
      map (ho_pattern_interpretation S G D (ho_polynomial_interpretation ps) (\<lambda>n. e (length D+n)) e) qs"
    by (rule map_cong; use PMeta.IH types in blast)
  have spine: "ho_polynomial_eval e (ho_meta_polynomial_spine T (HPVar (length D+n))
      (map (ho_meta_polynomial S G D ps) qs)) =
      foldl App (e (length D+n)) (map (\<lambda>q. ho_polynomial_eval e (ho_meta_polynomial S G D ps q)) qs)"
    using ho_meta_polynomial_spine_eval[OF typed _ head, of "map (ho_meta_polynomial S G D ps) qs" e "HPVar (length D+n)"]
    by (simp add: map_map o_def)
  show ?case using head by (simp add: spine args)
qed

end
