theory LP_Cut_NO_Permutation
 imports LP_Cut_NO_Renamed_Swap
begin

text \<open>Ordered transpositions extend a finite variable correspondence to a
total bijection. Their inverse uses the reversed order; a general permutation
need not be an involution. Saved alternatives are not in this output map.\<close>

fun lpc_no_permute where
 "lpc_no_permute [] z = z"
| "lpc_no_permute ((x,y)#swaps) z = lpc_no_permute swaps (lpc_no_swap x y z)"

lemma lpc_no_permute_append:
 "lpc_no_permute (xs @ ys) z = lpc_no_permute ys (lpc_no_permute xs z)"
 by (induct xs arbitrary: z) (auto split: prod.splits)

lemma lpc_no_permute_inverse[simp]:
 "lpc_no_permute (rev swaps) (lpc_no_permute swaps z) = z"
 by (induct swaps arbitrary: z)
   (auto simp: lpc_no_permute_append split: prod.splits)

lemma lpc_no_permute_inverse_other[simp]:
 "lpc_no_permute swaps (lpc_no_permute (rev swaps) z) = z"
 using lpc_no_permute_inverse[of "rev swaps" z] by simp

lemma lpc_no_permute_bij: "bij (lpc_no_permute swaps)"
 by (rule bijI, rule injI, metis lpc_no_permute_inverse,
     rule surjI[where f="lpc_no_permute (rev swaps)"])
   (simp add: fun_eq_iff)

definition lpc_no_permutation_support where
 "lpc_no_permutation_support swaps = set (map fst swaps) \<union> set (map snd swaps)"

lemma lpc_no_permutation_support_finite[simp]:
 "finite (lpc_no_permutation_support swaps)"
 by (simp add: lpc_no_permutation_support_def)

lemma lpc_no_permute_outside:
 "z\<notin>lpc_no_permutation_support swaps \<Longrightarrow> lpc_no_permute swaps z=z"
 by (induct swaps arbitrary: z)
   (auto simp: lpc_no_permutation_support_def lpc_no_swap_def split: prod.splits)

lemma lpc_no_permute_rename:
 assumes inverse: "\<And>z. p (p z) = z"
 shows "p (lpc_no_permute swaps z) =
   lpc_no_permute (map (\<lambda>(x,y). (p x,p y)) swaps) (p z)"
 by (induct swaps arbitrary: z)
   (auto simp: lpc_swap_rename_variable[OF inverse] split: prod.splits)

lemma lpc_mgu_resolve_output_permutation:
 fixes a :: "('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 shows "lpc_mgu_resolve a gs h bs
   (\<lambda>v. lp_isubst (sigma v) (\<lambda>w. LPIVar (lpc_no_permute swaps w)))
   (\<lambda>v. lp_isubst (rho v) (\<lambda>w. LPIVar (lpc_no_permute swaps w)))"
 using mgu
proof (induct swaps arbitrary: sigma rho)
 case Nil then show ?case by simp
next
 case (Cons pair swaps)
 obtain x y where pair: "pair=(x,y)" by (cases pair) auto
 note step = lpc_mgu_resolve_output_swap[OF Cons.prems, of x y]
 show ?case using Cons.hyps[OF step]
   by (simp add: pair lpc_isubst_comp)
qed

ML \<open>
val checked = [@{thm lpc_no_permute_bij}, @{thm lpc_no_permute_outside},
 @{thm lpc_no_permute_rename}, @{thm lpc_mgu_resolve_output_permutation}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted output permutation dependency" else ();
\<close>
end
