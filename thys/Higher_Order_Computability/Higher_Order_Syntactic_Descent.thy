theory Higher_Order_Syntactic_Descent
  imports Higher_Order_Recursive_Calls
begin

fun ho_app_subterm where
  "ho_app_subterm s (HApp f x) = (s=HApp f x \<or> ho_app_subterm s f \<or> ho_app_subterm s x)"
| "ho_app_subterm s t = (s=t)"

lemma ho_app_subterm_path:
  "ho_app_subterm s t \<Longrightarrow> ho_direct_application_subterm\<^sup>*\<^sup>* s t"
proof (induction t)
  case (HApp f x)
  have f: "ho_direct_application_subterm f (HApp f x)" and x: "ho_direct_application_subterm x (HApp f x)" by simp_all
  show ?case using HApp f x by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed auto

lemma ho_app_subterm_subst_path:
  "ho_app_subterm s t \<Longrightarrow>
    ho_direct_application_subterm\<^sup>*\<^sup>* (ho_subst q d s) (ho_subst q d t)"
proof (induction t)
  case (HApp f x)
  have f: "ho_direct_application_subterm (ho_subst q d f) (ho_subst q d (HApp f x))"
    and x: "ho_direct_application_subterm (ho_subst q d x) (ho_subst q d (HApp f x))" by simp_all
  show ?case using HApp f x by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed auto

lemma ho_app_proper_subterm_subst_path:
  "ho_app_subterm s t \<Longrightarrow> s\<noteq>t \<Longrightarrow>
    ho_direct_application_subterm\<^sup>+\<^sup>+ (ho_subst q d s) (ho_subst q d t)"
proof (induction t)
  case (HApp f x)
  have f: "ho_direct_application_subterm (ho_subst q d f) (ho_subst q d (HApp f x))"
    and x: "ho_direct_application_subterm (ho_subst q d x) (ho_subst q d (HApp f x))" by simp_all
  have "ho_app_subterm s f \<or> ho_app_subterm s x" using HApp.prems by simp
  then show ?case using ho_app_subterm_subst_path[where q=q and d=d] f x
    by (meson rtranclp_into_tranclp1)
qed auto

fun ho_lex_subterm where
  "ho_lex_subterm [] ys=False"
| "ho_lex_subterm (x#xs) []=False"
| "ho_lex_subterm (x#xs) (y#ys)=(length xs=length ys \<and>
    ((x=y \<and> ho_lex_subterm xs ys) \<or> (x\<noteq>y \<and> ho_app_subterm x y)))"

lemma ho_app_subterm_open_path:
  "ho_app_subterm s t \<Longrightarrow>
    ho_direct_application_subterm\<^sup>*\<^sup>* (ho_open q b d s) (ho_open q b d t)"
proof (induction t)
  case (HApp f x)
  have f: "ho_direct_application_subterm (ho_open q b d f) (ho_open q b d (HApp f x))"
    and x: "ho_direct_application_subterm (ho_open q b d x) (ho_open q b d (HApp f x))" by simp_all
  show ?case using HApp f x by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed auto

lemma ho_app_proper_subterm_open_path:
  "ho_app_subterm s t \<Longrightarrow> s\<noteq>t \<Longrightarrow>
    ho_direct_application_subterm\<^sup>+\<^sup>+ (ho_open q b d s) (ho_open q b d t)"
proof (induction t)
  case (HApp f x)
  have f: "ho_direct_application_subterm (ho_open q b d f) (ho_open q b d (HApp f x))"
    and x: "ho_direct_application_subterm (ho_open q b d x) (ho_open q b d (HApp f x))" by simp_all
  have "ho_app_subterm s f \<or> ho_app_subterm s x" using HApp.prems by simp
  then show ?case using ho_app_subterm_open_path[where q=q and b=b and d=d] f x
    by (meson rtranclp_into_tranclp1)
qed auto

context ho_source_neutral_reducibility
begin

lemma application_path_terminating_descent:
  assumes path: "ho_direct_application_subterm\<^sup>+\<^sup>+ u t"
    and acc: "Wellfounded.accp application_descent t"
  shows "(u,t)\<in>terminating_descent\<^sup>+"
  using path acc
proof (induction rule: tranclp_induct)
  case (base y)
  have edge: "application_descent u y" using base.hyps by (simp add: application_descent_def)
  have "(u,y)\<in>terminating_descent" using base.prems edge by (simp add: terminating_descent_def)
  then show ?case by (rule r_into_trancl)
next
  case (step y z)
  have edge: "application_descent y z" using step.hyps(2) by (simp add: application_descent_def)
  have ay: "Wellfounded.accp application_descent y" by (rule accp_downward[OF step.prems edge])
  have prefix: "(u,y)\<in>terminating_descent\<^sup>+" by (rule step.IH[OF ay])
  have last: "(y,z)\<in>terminating_descent" using step.prems edge by (simp add: terminating_descent_def)
  show ?case by (rule trancl_into_trancl[OF prefix last])
qed

lemma syntactic_lex_call_order:
  assumes lex: "ho_lex_subterm ys xs"
    and acc: "\<And>x. x\<in>set xs \<Longrightarrow> Wellfounded.accp application_descent (ho_subst s 0 x)"
    and ranks: "rank d=rank c"
  shows "((d,map (ho_subst s 0) ys),(c,map (ho_subst s 0) xs))\<in>call_order rank"
proof -
  have order: "(map (ho_subst s 0) ys,map (ho_subst s 0) xs)\<in>lex (terminating_descent\<^sup>+)"
    using lex acc
  proof (induction ys arbitrary: xs)
    case Nil
    then show ?case by simp
  next
    case (Cons y ys)
    obtain x zs where xs: "xs=x#zs" using Cons.prems(1) by (cases xs) auto
    have len: "length ys=length zs" using Cons.prems(1) unfolding xs by simp
    show ?case
    proof (cases "y=x")
      case True
      have rec: "ho_lex_subterm ys zs" using Cons.prems(1) True unfolding xs by simp
      have a: "Wellfounded.accp application_descent (ho_subst s 0 z)" if "z\<in>set zs" for z
        using Cons.prems(2) that xs by simp
      show ?thesis using Cons.IH[OF rec a] unfolding xs True by simp
    next
      case False
      have sub: "ho_app_subterm y x" using Cons.prems(1) False unfolding xs by simp
      have path: "ho_direct_application_subterm\<^sup>+\<^sup>+ (ho_subst s 0 y) (ho_subst s 0 x)"
        by (rule ho_app_proper_subterm_subst_path[OF sub False])
      have a: "Wellfounded.accp application_descent (ho_subst s 0 x)" using Cons.prems(2) xs by simp
      have small: "(ho_subst s 0 y,ho_subst s 0 x)\<in>terminating_descent\<^sup>+"
        by (rule application_path_terminating_descent[OF path a])
      show ?thesis using small len unfolding xs by simp
    qed
  qed
  show ?thesis using order ranks by (simp add: call_order_def inv_image_def lex_prod_def)
qed

lemma syntactic_lex_open_call_order:
  assumes lex: "ho_lex_subterm ys xs"
    and acc: "\<And>x. x\<in>set xs \<Longrightarrow> Wellfounded.accp application_descent (ho_open s b 0 x)"
    and ranks: "rank d=rank c"
  shows "((d,map (ho_open s b 0) ys),(c,map (ho_open s b 0) xs))\<in>call_order rank"
proof -
  have order: "(map (ho_open s b 0) ys,map (ho_open s b 0) xs)\<in>lex (terminating_descent\<^sup>+)"
    using lex acc
  proof (induction ys arbitrary: xs)
    case Nil
    then show ?case by simp
  next
    case (Cons y ys)
    obtain x zs where xs: "xs=x#zs" using Cons.prems(1) by (cases xs) auto
    have len: "length ys=length zs" using Cons.prems(1) unfolding xs by simp
    show ?case
    proof (cases "y=x")
      case True
      have rec: "ho_lex_subterm ys zs" using Cons.prems(1) True unfolding xs by simp
      have a: "Wellfounded.accp application_descent (ho_open s b 0 z)" if "z\<in>set zs" for z
        using Cons.prems(2) that xs by simp
      show ?thesis using Cons.IH[OF rec a] unfolding xs True by simp
    next
      case False
      have sub: "ho_app_subterm y x" using Cons.prems(1) False unfolding xs by simp
      have path: "ho_direct_application_subterm\<^sup>+\<^sup>+ (ho_open s b 0 y) (ho_open s b 0 x)"
        by (rule ho_app_proper_subterm_open_path[OF sub False])
      have a: "Wellfounded.accp application_descent (ho_open s b 0 x)" using Cons.prems(2) xs by simp
      have small: "(ho_open s b 0 y,ho_open s b 0 x)\<in>terminating_descent\<^sup>+"
        by (rule application_path_terminating_descent[OF path a])
      show ?thesis using small len unfolding xs by simp
    qed
  qed
  show ?thesis using order ranks by (simp add: call_order_def inv_image_def lex_prod_def)
qed

end

end
