theory Higher_Order_Guarded_Calls
  imports Higher_Order_Guarded_Terms
begin

lemma guard_blocked_open:
  assumes block: "ho_guard_blocked F R c xs"
    and closed: "list_all (ho_bound_closed 0) xs"
  shows "ho_guard_blocked F R c (map (ho_open s b 0) xs)"
proof -
  have clash: "ho_guard_clash F (map (ho_open s b 0) xs) ls"
    if input: "ho_guard_clash F xs ls" for ls
  proof -
    obtain i where i: "i<length xs" "i<length ls"
      and g: "ho_guard_lambda F (xs!i)" and p: "ho_constant_abstraction (ls!i)"
      using input unfolding ho_guard_clash_def by blast
    have cc: "ho_bound_closed 0 (xs!i)"
      using closed i(1) by (simp add: list_all_length)
    have eq: "ho_open s b 0 (xs!i)=xs!i" by (rule guard_lambda_open[OF g cc])
    show ?thesis unfolding ho_guard_clash_def
      by (rule exI[of _ i]) (use i g p eq in simp)
  qed
  show ?thesis using block
    unfolding ho_guard_blocked_def list_all_iff by (auto intro: clash)
qed

context ho_source_accessible_reducibility
begin

lemma guard_clash_arguments_step:
  assumes rules: "ho_guard_rules F R"
    and clash: "ho_guard_clash F xs ls"
    and step: "ho_arguments_step S V R B xs ys"
  shows "ho_guard_clash F ys ls"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs"
    and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain i where i: "i<length xs" "i<length ls"
    and g: "ho_guard_lambda F (xs!i)" and p: "ho_constant_abstraction (ls!i)"
    using clash unfolding ho_guard_clash_def by blast
  have update: "ys=xs[length us:=w]" by (simp add: xs ys list_update_append)
  have len: "length ys=length xs" by (simp add: xs ys)
  have out: "ho_guard_lambda F (ys!i)"
  proof (cases "i=length us")
    case True
    have gv: "ho_guard_lambda F v" using g True xs by simp
    have gw: "ho_guard_lambda F w" by (rule guard_lambda_step[OF rules vw gv])
    show ?thesis using True ys gw by simp
  next
    case False
    show ?thesis using g False update by simp
  qed
  show ?thesis unfolding ho_guard_clash_def
    by (rule exI[of _ i]) (use i p out len in simp)
qed

lemma guard_blocked_arguments_step:
  assumes rules: "ho_guard_rules F R"
    and block: "ho_guard_blocked F R c xs"
    and step: "ho_arguments_step S V R B xs ys"
  shows "ho_guard_blocked F R c ys"
  using block unfolding ho_guard_blocked_def list_all_iff
  by (auto intro: guard_clash_arguments_step[OF rules _ step])

lemma guard_blocked_no_root:
  assumes block: "ho_guard_blocked F R c xs"
  shows "\<not>ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
proof
  assume root: "ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
  obtain G l r s where member: "(G,l,r)\<in>set R"
    and inst: "ho_instantiate s 0 l=Some (ho_apply_terms (HConst c) xs)"
    using root unfolding ho_root_step_def by blast
  have head: "ho_application_head (ho_erase_pattern l)=HConst c"
    using rule_instance_head_spine(1)[OF member inst] by simp
  have zero_l: "ho_zero_arity_pattern l"
    using zero member unfolding ho_zero_arity_rules_def by auto
  have eq: "ho_subst s 0 (ho_erase_pattern l)=ho_apply_terms (HConst c) xs"
    using inst ho_zero_arity_instantiate[OF zero_l, of s 0] by simp
  have args: "map (ho_subst s 0) (ho_spine_arguments (ho_erase_pattern l))=xs"
    using ho_constant_arguments_subst[OF head, of s 0] eq by simp
  have clash: "ho_guard_clash F xs (ho_spine_arguments (ho_erase_pattern l))"
    using block member head by (auto simp: ho_guard_blocked_def list_all_iff)
  obtain i where i: "i<length xs" "i<length (ho_spine_arguments (ho_erase_pattern l))"
    and g: "ho_guard_lambda F (xs!i)"
    and p: "ho_constant_abstraction (ho_spine_arguments (ho_erase_pattern l)!i)"
    using clash unfolding ho_guard_clash_def by blast
  have inst_arg: "xs!i=ho_subst s 0 (ho_spine_arguments (ho_erase_pattern l)!i)"
    using args i(2) by (metis nth_map)
  show False using guard_constant_abstraction_subst[OF p, of F s] g inst_arg by simp
qed

corollary guard_blocked_calls_computable:
  assumes arities: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity d"
    and bound: "arity c\<le>length (ho_argument_types T)"
    and symbol: "ho_lookup S c=Some T"
    and rules: "ho_guard_rules F R"
    and block: "ho_guard_blocked F R c xs"
    and args: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
  shows "source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
proof (rule blocked_calls_computable[where P="ho_guard_blocked F R c" and arity=arity])
  show "ho_spine_length (ho_erase_pattern l)=arity d"
    if "(G,l,r)\<in>set R" "ho_application_head (ho_erase_pattern l)=HConst d" for G l r d
    by (rule arities[OF that])
  show "arity c\<le>length (ho_argument_types T)" by (rule bound)
  show "ho_lookup S c=Some T" by (rule symbol)
  show "ho_guard_blocked F R c ys"
    if "ho_guard_blocked F R c xs" "ho_arguments_step S V R B xs ys" for xs ys
    by (rule guard_blocked_arguments_step[OF rules that])
  show "\<not>ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
    if "ho_guard_blocked F R c xs" for xs u
    by (rule guard_blocked_no_root[OF that])
  show "ho_guard_blocked F R c xs" by (rule block)
  show "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs" by (rule args)
qed

end
end
