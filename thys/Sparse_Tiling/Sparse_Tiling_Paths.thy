theory Sparse_Tiling_Paths
  imports Sparse_Tiling_Simulation
begin

fun sparse_run :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sparse_run q [] = q"
| "sparse_run q (a # w) = sparse_run (drop 1 (q @ [a])) w"

fun sparse_path :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "sparse_path q [] = []"
| "sparse_path q (a # w) = (q @ [a]) # sparse_path (drop 1 (q @ [a])) w"

lemma sparse_run_append:
  "sparse_run q (u @ v) = sparse_run (sparse_run q u) v"
  by (induction u arbitrary: q) auto

lemma sparse_path_append:
  "sparse_path q (u @ v) = sparse_path q u @ sparse_path (sparse_run q u) v"
  by (induction u arbitrary: q) auto

lemma sparse_run_length [simp]: "length (sparse_run q w) = length q"
  by (induction w arbitrary: q) auto

lemma sparse_run_suffix:
  "sparse_run q w = drop (length w) (q @ w)"
proof (induction w rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc a w)
  have aux: "drop (length w) ((q @ w) @ [a]) = drop (length w) (q @ w) @ [a]"
    by (subst drop_append) simp
  have "sparse_run q (w @ [a]) = drop 1 (drop (length w) (q @ w) @ [a])"
    by (simp only: sparse_run_append sparse_run.simps snoc.IH)
  also have "... = drop 1 (drop (length w) ((q @ w) @ [a]))"
    by (simp only: aux)
  also have "... = drop (length (w @ [a])) (q @ (w @ [a]))"
    by (simp only: drop_drop length_append list.size add_0 append_assoc add.commute One_nat_def)
  finally show ?case .
qed

lemma sparse_run_synchronizes:
  assumes "length y = length q"
  shows "sparse_run q (w @ y) = y"
  using assms by (simp add: sparse_run_append sparse_run_suffix drop_append)

lemma sparse_run_exact:
  "length y = length q \<Longrightarrow> sparse_run q y = y"
  using sparse_run_synchronizes[of y q "[]"] by simp

lemma sparse_path_context:
  assumes "length y = length q"
  shows "sparse_path q (u @ l @ y @ v) =
    sparse_path q u @ sparse_path (sparse_run q u) (l @ y) @ sparse_path y v"
  using assms
  by (simp add: sparse_path_append sparse_run_append sparse_run_exact)

lemma sparse_path_rewrite_simulation:
  assumes width: "length y = length q"
    and rule: "(sparse_path (sparse_run q u) (l @ y),
                sparse_path (sparse_run q u) (r @ y)) \<in> T"
  shows "(sparse_path q (u @ l @ y @ v), sparse_path q (u @ r @ y @ v))
    \<in> sparse_word_step T"
proof -
  have "(sparse_path q u @ sparse_path (sparse_run q u) (l @ y) @ sparse_path y v,
         sparse_path q u @ sparse_path (sparse_run q u) (r @ y) @ sparse_path y v)
    \<in> sparse_word_step T"
    by (rule sparse_word_stepI[OF rule])
  then show ?thesis by (simp only: sparse_path_context[OF width])
qed

end
