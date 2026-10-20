theory Higher_Order_Expansion_Recursive
  imports Higher_Order_Expansion_Closure
begin

definition ho_expansion_recursive_branch where
  "ho_expansion_recursive_branch S G ps ms ofuel prec arity c ls recur t=
    (case ho_application_head t of HConst d \<Rightarrow>
      (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
        prec d=prec c \<and>
        ho_typeof S G [] t=Some (ho_drop_type (arity d) U) \<and>
        list_all2 (\<lambda>T x. ho_typeof S G [] x=Some T)
          (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
        ho_check_call_comparison S ps ms ofuel G c ls d (ho_spine_arguments t) True \<and>
        list_all recur (ho_spine_arguments t))
    | _ \<Rightarrow> False)"

context ho_source_accessible_reducibility
begin

lemma ho_expansion_recursive_branch_sound:
  assumes ps: "ho_check_polynomial_signature S ps"
    and ms: "ho_check_polynomial_signature S ms"
    and ev: "ho_env_value (B@V) e"
    and weight_eq: "weight=ho_call_weight S V B (ho_polynomial_interpretation ps) (ho_polynomial_interpretation ms) e"
    and checked: "ho_expansion_recursive_branch S G ps ms ofuel prec arity c ls recur t"
    and ty: "ho_typeof S G [] t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and rec: "\<And>u T. recur u \<Longrightarrow> ho_typeof S G [] u=Some T \<Longrightarrow>
      source_candidate T (ho_subst s 0 u)"
    and smaller: "\<And>d ys U. ((d,ys),(c,map (ho_subst s 0) ls))\<in>semantic_call_order prec weight priority \<Longrightarrow>
      ho_lookup S d=Some U \<Longrightarrow> list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
      source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
  shows "source_candidate A (ho_subst s 0 t)"
proof -
  obtain d U where head: "ho_application_head t=HConst d" and ds: "ho_lookup S d=Some U"
    and precedence: "prec d=prec c" and eq: "A=ho_drop_type (arity d) U"
    and types: "list_all2 (\<lambda>T x. ho_typeof S G [] x=Some T)
      (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
    and comparison: "ho_check_call_comparison S ps ms ofuel G c ls d (ho_spine_arguments t) True"
    and children: "list_all recur (ho_spine_arguments t)"
    using checked ty unfolding ho_expansion_recursive_branch_def
    by (auto split: ho_term.split_asm option.split_asm)
  have typed_checked: "list_all2 (\<lambda>T x. ho_typeof S G [] x=Some T \<and> recur x)
      (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
    using types children by (induction rule: list_all2_induct) auto
  have args: "list_all2 source_candidate (take (arity d) (ho_argument_types U))
      (map (ho_subst s 0) (ho_spine_arguments t))"
    using typed_checked by (induction rule: list_all2_induct) (auto intro: rec)
  have closed: "list_all (ho_bound_closed 0) (ho_spine_arguments t)"
    using types by (induction rule: list_all2_induct) (auto dest: ho_typeof_bound_closed)
  have mapped: "map (ho_open s HBound 0) (ho_spine_arguments t)=
      map (ho_subst s 0) (ho_spine_arguments t)"
    by (rule map_cong[OF refl]) (use closed in \<open>auto simp: list_all_iff intro: ho_open_closed\<close>)
  have strict: "weight d (map (ho_subst s 0) (ho_spine_arguments t))<
      weight c (map (ho_subst s 0) ls)"
    using ho_check_call_comparison_sound[where b=HBound, OF ps ms comparison subst ev]
      weight_eq mapped by simp
  have small: "((d,map (ho_subst s 0) (ho_spine_arguments t)),(c,map (ho_subst s 0) ls))
      \<in>semantic_call_order prec weight priority"
    by (rule semantic_strict_call_order[where prec=prec and weight=weight and c=c and d=d,
      OF precedence strict])
  have child: "source_candidate (ho_drop_type (arity d) U)
      (ho_apply_terms (HConst d) (map (ho_subst s 0) (ho_spine_arguments t)))"
    by (rule smaller[OF small ds args])
  have rewrite: "ho_subst s 0 t=ho_apply_terms (HConst d) (map (ho_subst s 0) (ho_spine_arguments t))"
    using ho_subst_apply_terms[of s 0 "ho_application_head t" "ho_spine_arguments t"]
      ho_spine_reconstruct[of t] head by simp
  show ?thesis using child eq rewrite by simp
qed

end
end
