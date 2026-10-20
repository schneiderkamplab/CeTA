theory Higher_Order_Expansion_Semantic
  imports Higher_Order_Expansion_Recursive
begin

definition ho_check_call_semantic_closure where
  "ho_check_call_semantic_closure S G R K defs obs sorts ps ms ofuel prec priority arity c ls fuel efuel t=
    ho_check_expansion_closure S G R sorts defs obs
      (\<lambda>u. (\<forall>T\<in>ho_binder_types u. ho_type_bases T\<subseteq>K) \<and>
        ho_check_semantic_closure S G sorts ps ms ofuel prec priority arity c ls fuel [] u)
      (ho_expansion_recursive_branch S G ps ms ofuel prec arity c ls) efuel t"

context ho_source_accessible_reducibility
begin

theorem ho_check_call_semantic_closure_sound:
  assumes ps: "ho_check_polynomial_signature S ps"
    and ms: "ho_check_polynomial_signature S ms"
    and ev: "ho_env_value (B@V) e"
    and weight_eq: "weight=ho_call_weight S V B (ho_polynomial_interpretation ps) (ho_polynomial_interpretation ms) e"
    and check: "ho_check_call_semantic_closure S G R K defs obs rank ps ms ofuel prec priority arity c ls fuel efuel t"
    and ty: "ho_typeof S G [] t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and closed: "\<And>l. l\<in>set ls \<Longrightarrow> ho_bound_closed 0 l"
    and bounds: "\<And>d U. ho_lookup S d=Some U \<Longrightarrow> arity d\<le>length (ho_argument_types U)"
    and lhs_typed: "\<And>l. l\<in>set ls \<Longrightarrow> \<exists>T. ho_typeof S G [] l=Some T"
    and known: "\<And>l. l\<in>set ls \<Longrightarrow> \<exists>T. source_candidate T (ho_subst s 0 l)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source_candidate (HBase b) x"
    and types_inhabited: "\<And>T. ho_type_bases T\<subseteq>K \<Longrightarrow> \<exists>x. source_candidate T x"
    and smaller: "\<And>d ys U. ((d,ys),(c,map (ho_subst s 0) ls))\<in>semantic_call_order prec weight priority \<Longrightarrow>
      ho_lookup S d=Some U \<Longrightarrow> list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
      source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
  shows "source_candidate A (ho_subst s 0 t)"
proof (rule ho_check_expansion_closure_sound[OF _ ty subst])
  show "ho_check_expansion_closure S G R rank defs obs
      (\<lambda>u. (\<forall>T\<in>ho_binder_types u. ho_type_bases T\<subseteq>K) \<and>
        ho_check_semantic_closure S G rank ps ms ofuel prec priority arity c ls fuel [] u)
      (ho_expansion_recursive_branch S G ps ms ofuel prec arity c ls) efuel t"
    using check unfolding ho_check_call_semantic_closure_def .
  show "source_candidate T (ho_subst s 0 u)"
    if recursive: "\<And>x U. recur x \<Longrightarrow> ho_typeof S G [] x=Some U \<Longrightarrow>
        source_candidate U (ho_subst s 0 x)"
      and ck: "ho_expansion_recursive_branch S G ps ms ofuel prec arity c ls recur u"
      and ut: "ho_typeof S G [] u=Some T" for recur u T
    by (rule ho_expansion_recursive_branch_sound[OF ps ms ev weight_eq ck ut subst recursive smaller])
  fix u T
  assume leaf: "(\<forall>Z\<in>ho_binder_types u. ho_type_bases Z\<subseteq>K) \<and>
      ho_check_semantic_closure S G rank ps ms ofuel prec priority arity c ls fuel [] u"
    and ut: "ho_typeof S G [] u=Some T"
  have checked: "ho_check_semantic_closure S G rank ps ms ofuel prec priority arity c ls fuel [] u"
    using leaf by blast
  have binders: "\<exists>x. source_candidate Z x" if "Z\<in>ho_binder_types u" for Z
    by (rule types_inhabited) (use leaf that in blast)
  have comp: "source_candidate T (ho_open s HBound 0 u)"
    by (rule ho_check_semantic_closure_sound[where b=HBound,
      OF ps ms ev weight_eq checked ut subst _ closed binders bounds lhs_typed known inhabited smaller]) simp
  have uc: "ho_bound_closed 0 u" using ho_typeof_bound_closed[OF ut] by simp
  show "source_candidate T (ho_subst s 0 u)" using comp ho_open_closed[OF uc, of s HBound] by simp
qed

end
end
