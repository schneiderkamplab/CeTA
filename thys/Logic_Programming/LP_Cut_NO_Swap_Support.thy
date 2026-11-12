theory LP_Cut_NO_Swap_Support
 imports LP_Cut_NO_Renamed_Swap
begin

lemma lpc_conjugate_supported_outside:
 assumes inverse: "\<And>z. p (p z) = z"
   and support: "\<And>z. z\<notin>S \<Longrightarrow> substitution z = Var z"
   and outside: "z\<notin>p ` S"
 shows "lpc_conjugate_substitution p substitution z = Var z"
proof -
 have preimage_outside: "p z\<notin>S"
 proof
   assume "p z\<in>S"
   then have "p (p z)\<in>p ` S" by (rule imageI)
   then show False using outside by (simp add: inverse)
 qed
 show ?thesis by (simp add: lpc_conjugate_substitution_def support[OF preimage_outside] inverse o_def)
qed

lemma lpc_swapped_substitution_support:
 assumes lengths: "length V=length images"
   and outside: "z\<notin>set V \<union> {x,y}"
 shows "(lpc_mgu_substitution V images z)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)) = Var z"
 using outside by (simp add: lpc_mgu_substitution_outside[OF lengths] lpc_no_swap_def)

lemma lpc_conjugate_swapped_substitution:
 assumes inverse: "\<And>z. p (p z) = z"
 shows "lpc_conjugate_substitution p
   (\<lambda>z. (substitution z)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v))) z =
   (lpc_conjugate_substitution p substitution z)\<cdot>(\<lambda>v. Var (lpc_no_swap (p x) (p y) v))"
 by (simp add: lpc_conjugate_substitution_def lpc_swap_rename_term[OF inverse])

lemma lpc_renamed_swap_fixes_ambient:
 assumes inverse: "\<And>z. p (p z) = z"
   and lengths: "length V=length images"
   and outside: "\<And>z. z\<in>\<Union>(vars_term ` set extra) \<Longrightarrow>
     z\<notin>p ` (set V \<union> {x,y})"
 shows "map (\<lambda>t. (t\<cdot>lpc_conjugate_substitution p (lpc_mgu_substitution V images))\<cdot>
   (\<lambda>v. Var (lpc_no_swap (p x) (p y) v))) extra = extra"
proof -
 let ?sub = "\<lambda>z. (lpc_mgu_substitution V images z)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v))"
 have fixed: "map (\<lambda>t. t\<cdot>lpc_conjugate_substitution p ?sub) extra = extra"
   by (rule lpc_substitution_fixes_ambient_terms,
     rule lpc_conjugate_supported_outside[where S="set V \<union> {x,y}" and substitution="?sub", OF inverse],
     rule lpc_swapped_substitution_support[OF lengths], assumption, rule outside)
 have applied: "t\<cdot>lpc_conjugate_substitution p ?sub =
   (t\<cdot>lpc_conjugate_substitution p (lpc_mgu_substitution V images))\<cdot>
     (\<lambda>v. Var (lpc_no_swap (p x) (p y) v))" for t
   by (induct t) (auto simp: lpc_conjugate_swapped_substitution[OF inverse] intro!: map_cong)
 show ?thesis using fixed by (simp only: applied)
qed

ML \<open>
val checked = [@{thm lpc_conjugate_supported_outside}, @{thm lpc_swapped_substitution_support},
 @{thm lpc_conjugate_swapped_substitution}, @{thm lpc_renamed_swap_fixes_ambient}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite output-swap support" else ();
\<close>
end
