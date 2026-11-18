theory LP_Prolog_List_Leaf_Effect
 imports LP_Prolog_Leaf_Lexicographic_Return LP_Prolog_Structural_Univ
begin

text \<open>A proper observed list spine is retained by the leaf effect.
Only element observations can change; a finite spine does not by itself
supply finite element observations or a helper termination proof.\<close>

lemma lpp_leaf_effect_constructor_iff:
 "lpp_leaf_effect A (Fun (Inl f) xs) t \<longleftrightarrow>
   (\<exists>ys. t=Fun (Inl f) ys \<and> list_all2 (lpp_leaf_effect A) xs ys)"
 by (auto elim: lpp_leaf_effect.cases intro: lpp_leaf_effect.constructor)

lemma lpp_list_leaf_effect_exact:
 "lpp_leaf_effect A (lpp_structural_argument_list xs) t \<longleftrightarrow>
   (\<exists>ys. t=lpp_structural_argument_list ys \<and> list_all2 (lpp_leaf_effect A) xs ys)"
proof (induct xs arbitrary: t)
 case Nil
 then show ?case by (auto simp: lpp_leaf_effect_constructor_iff)
next
 case (Cons x xs)
 show ?case using Cons.hyps
  apply (auto simp: lpp_leaf_effect_constructor_iff list_all2_Cons1 split: list.splits)
  subgoal for z ysa by (rule exI[of _ "z#ysa"]) auto
  done
qed

lemma lpp_list_leaf_effect_length:
 assumes effect: "lpp_leaf_effect A (lpp_structural_argument_list xs) t"
 shows "\<exists>ys. t=lpp_structural_argument_list ys \<and>
  length ys=length xs \<and> list_all2 (lpp_leaf_effect A) xs ys"
proof -
 obtain ys where shape: "t=lpp_structural_argument_list ys"
  and related: "list_all2 (lpp_leaf_effect A) xs ys"
  using effect by (auto simp: lpp_list_leaf_effect_exact)
 have lengths: "length ys=length xs" using list_all2_lengthD[OF related] by simp
 show ?thesis by (rule exI[of _ ys]) (use shape related lengths in auto)
qed

ML \<open>
val checked = @{thms lpp_leaf_effect_constructor_iff lpp_list_leaf_effect_exact lpp_list_leaf_effect_length};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted list leaf return" else ();
\<close>
end
