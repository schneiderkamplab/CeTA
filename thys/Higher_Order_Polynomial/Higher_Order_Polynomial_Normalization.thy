theory Higher_Order_Polynomial_Normalization
  imports Higher_Order_Polynomial
begin

fun ho_polynomial_rename where
  "ho_polynomial_rename r (HPVar n) = HPVar (r n)"
| "ho_polynomial_rename r (HPNumber b n) = HPNumber b n"
| "ho_polynomial_rename r (HPAdd b p q) = HPAdd b (ho_polynomial_rename r p) (ho_polynomial_rename r q)"
| "ho_polynomial_rename r (HPMultiply b p q) = HPMultiply b (ho_polynomial_rename r p) (ho_polynomial_rename r q)"
| "ho_polynomial_rename r (HPApply A B f x) = HPApply A B (ho_polynomial_rename r f) (ho_polynomial_rename r x)"
| "ho_polynomial_rename r (HPAbstract A B t) = HPAbstract A B (ho_polynomial_rename (ho_rename_up r) t)"

lemma ho_polynomial_eval_rename:
  "ho_polynomial_eval e (ho_polynomial_rename r p) = ho_polynomial_eval (\<lambda>n. e (r n)) p"
  by (induction p arbitrary: e r) (simp_all add: ho_env_lift_rename)

definition ho_polynomial_subst_up where
  "ho_polynomial_subst_up s n = (case n of 0 \<Rightarrow> HPVar 0 | Suc k \<Rightarrow> ho_polynomial_rename Suc (s k))"

fun ho_polynomial_subst where
  "ho_polynomial_subst s (HPVar n) = s n"
| "ho_polynomial_subst s (HPNumber b n) = HPNumber b n"
| "ho_polynomial_subst s (HPAdd b p q) = HPAdd b (ho_polynomial_subst s p) (ho_polynomial_subst s q)"
| "ho_polynomial_subst s (HPMultiply b p q) = HPMultiply b (ho_polynomial_subst s p) (ho_polynomial_subst s q)"
| "ho_polynomial_subst s (HPApply A B f x) = HPApply A B (ho_polynomial_subst s f) (ho_polynomial_subst s x)"
| "ho_polynomial_subst s (HPAbstract A B t) = HPAbstract A B (ho_polynomial_subst (ho_polynomial_subst_up s) t)"

lemma ho_polynomial_eval_subst_up:
  "ho_polynomial_eval (ho_env_lift e) (ho_polynomial_subst_up s n) =
    ho_env_lift (\<lambda>i. ho_polynomial_eval e (s i)) n"
  by (cases n) (simp_all add: ho_polynomial_subst_up_def ho_polynomial_eval_rename
    ho_env_lift_def ho_env_cons_def ho_polynomial_eval_lift)

lemma ho_polynomial_eval_parallel_subst:
  "ho_polynomial_eval e (ho_polynomial_subst s p) = ho_polynomial_eval (\<lambda>n. ho_polynomial_eval e (s n)) p"
  by (induction p arbitrary: e s) (simp_all add: ho_polynomial_eval_subst_up)

definition ho_polynomial_beta_subst where
  "ho_polynomial_beta_subst x t =
    ho_polynomial_subst (\<lambda>n. case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> HPVar k) t"

lemma ho_polynomial_eval_beta_subst:
  "ho_polynomial_eval e (ho_polynomial_beta_subst x t) =
    ho_polynomial_eval (ho_env_cons (ho_polynomial_eval e x) e) t"
proof -
  have env: "(\<lambda>n. ho_polynomial_eval e (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> HPVar k)) =
      ho_env_cons (ho_polynomial_eval e x) e"
    by (rule ext; rename_tac n; case_tac n) (simp_all add: ho_env_cons_def)
  show ?thesis by (simp add: ho_polynomial_beta_subst_def ho_polynomial_eval_parallel_subst env)
qed

lemma ho_polynomial_beta_path:
  "beta\<^sup>*\<^sup>* (ho_polynomial_eval e (HPApply A B (HPAbstract C D t) x))
    (ho_polynomial_eval e (ho_polynomial_beta_subst x t))"
  unfolding ho_polynomial_eval_beta_subst ho_polynomial_eval.simps(5)
  by (rule r_into_rtranclp) (rule ho_polynomial_abstraction_beta)

fun ho_polynomial_contract where
  "ho_polynomial_contract (HPApply A B (HPAbstract C D t) x) = ho_polynomial_beta_subst x t"
| "ho_polynomial_contract (HPAdd b (HPNumber c n) (HPNumber d m)) = HPNumber b (n+m)"
| "ho_polynomial_contract (HPMultiply b (HPNumber c n) (HPNumber d m)) = HPNumber b (n*m)"
| "ho_polynomial_contract p = p"

lemma ho_polynomial_contract_path:
  "beta\<^sup>*\<^sup>* (ho_polynomial_eval e p) (ho_polynomial_eval e (ho_polynomial_contract p))"
  by (cases p rule: ho_polynomial_contract.cases)
     (auto intro: ho_polynomial_beta_path[simplified] ho_add_church ho_multiply_church)

fun ho_polynomial_normalize where
  "ho_polynomial_normalize 0 p = p"
| "ho_polynomial_normalize (Suc n) (HPVar k) = HPVar k"
| "ho_polynomial_normalize (Suc n) (HPNumber b k) = HPNumber b k"
| "ho_polynomial_normalize (Suc n) (HPAdd b p q) = ho_polynomial_contract
    (HPAdd b (ho_polynomial_normalize n p) (ho_polynomial_normalize n q))"
| "ho_polynomial_normalize (Suc n) (HPMultiply b p q) = ho_polynomial_contract
    (HPMultiply b (ho_polynomial_normalize n p) (ho_polynomial_normalize n q))"
| "ho_polynomial_normalize (Suc n) (HPApply A B f x) =
    (let q = HPApply A B (ho_polynomial_normalize n f) (ho_polynomial_normalize n x);
         r = ho_polynomial_contract q
     in if r=q then q else ho_polynomial_normalize n r)"
| "ho_polynomial_normalize (Suc n) (HPAbstract A B t) =
    HPAbstract A B (ho_polynomial_normalize n t)"

theorem ho_polynomial_normalize_path:
  "beta\<^sup>*\<^sup>* (ho_polynomial_eval e p) (ho_polynomial_eval e (ho_polynomial_normalize n p))"
proof (induction n arbitrary: p e)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases p)
    case (HPVar k)
    then show ?thesis by simp
  next
    case (HPNumber b k)
    then show ?thesis by simp
  next
    case (HPAdd b q r)
    have children: "beta\<^sup>*\<^sup>* (ho_polynomial_eval e p)
      (ho_polynomial_eval e (HPAdd b (ho_polynomial_normalize n q) (ho_polynomial_normalize n r)))"
      unfolding HPAdd ho_polynomial_eval.simps by (rule ho_add_betas[OF Suc.IH Suc.IH])
    show ?thesis using rtranclp_trans[OF children ho_polynomial_contract_path] by (simp add: HPAdd)
  next
    case (HPMultiply b q r)
    have children: "beta\<^sup>*\<^sup>* (ho_polynomial_eval e p)
      (ho_polynomial_eval e (HPMultiply b (ho_polynomial_normalize n q) (ho_polynomial_normalize n r)))"
      unfolding HPMultiply ho_polynomial_eval.simps by (rule ho_multiply_betas[OF Suc.IH Suc.IH])
    show ?thesis using rtranclp_trans[OF children ho_polynomial_contract_path] by (simp add: HPMultiply)
  next
    case (HPApply A B f x)
    let ?q = "HPApply A B (ho_polynomial_normalize n f) (ho_polynomial_normalize n x)"
    have children: "beta\<^sup>*\<^sup>* (ho_polynomial_eval e p) (ho_polynomial_eval e ?q)"
      unfolding HPApply ho_polynomial_eval.simps by (rule rtrancl_beta_App[OF Suc.IH Suc.IH])
    have contraction: "beta\<^sup>*\<^sup>* (ho_polynomial_eval e p) (ho_polynomial_eval e (ho_polynomial_contract ?q))"
      by (rule rtranclp_trans[OF children ho_polynomial_contract_path])
    have further: "beta\<^sup>*\<^sup>* (ho_polynomial_eval e p)
        (ho_polynomial_eval e (ho_polynomial_normalize n (ho_polynomial_contract ?q)))"
      by (rule rtranclp_trans[OF contraction Suc.IH])
    show ?thesis using children further by (simp add: HPApply Let_def)
  next
    case (HPAbstract A B t)
    show ?thesis unfolding HPAbstract ho_polynomial_normalize.simps ho_polynomial_eval.simps
      by (rule rtrancl_beta_Abs[OF Suc.IH])
  qed
qed

end
