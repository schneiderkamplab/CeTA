theory Sparse_Tiling_Windows
  imports Sparse_Tiling_Paths
begin

fun sparse_windows :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "sparse_windows n [] = []"
| "sparse_windows n (a # w) =
    (if n \<le> length (a # w) then take n (a # w) # sparse_windows n w else [])"

lemma sparse_windows_short:
  "length w < n \<Longrightarrow> sparse_windows n w = []"
  by (cases w) auto

lemma sparse_windows_step:
  "sparse_windows (Suc (length q)) (q @ a # w) =
    (q @ [a]) # sparse_windows (Suc (length q)) (drop 1 (q @ [a]) @ w)"
  by (cases q) auto

lemma sparse_windows_path:
  "sparse_windows (Suc (length q)) (q @ w) = sparse_path q w"
proof (induction w arbitrary: q)
  case Nil
  then show ?case by (simp add: sparse_windows_short)
next
  case (Cons a w)
  have length: "length (drop 1 (q @ [a])) = length q" by simp
  have tail: "sparse_windows (Suc (length q)) (drop 1 (q @ [a]) @ w) =
      sparse_path (drop 1 (q @ [a])) w"
    using Cons.IH[of "drop 1 (q @ [a])"] by (simp only: length)
  show ?case by (simp only: sparse_windows_step sparse_path.simps tail)
qed

end
