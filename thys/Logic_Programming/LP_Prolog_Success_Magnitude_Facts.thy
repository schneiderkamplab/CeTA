theory LP_Prolog_Success_Magnitude_Facts
 imports LP_Prolog_Success_Magnitude
begin

lemma lpp_magnitude_list_all2_member:
  "list_all2 R xs ys \<Longrightarrow> x\<in>set xs \<Longrightarrow> \<exists>y. R x y"
  by (induction rule: list_all2_induct) auto

fun lpp_magnitude_max where
  "lpp_magnitude_max operation [] = 0"
| "lpp_magnitude_max operation (a#as) = max (abs (lpp_stable_scaled_bound operation a))
    (lpp_magnitude_max operation as)"

lemma lpp_magnitude_max_nonnegative: "0\<le>lpp_magnitude_max operation ts"
  by (induction ts) auto

lemma lpp_magnitude_max_upper:
  "t\<in>set ts \<Longrightarrow> abs (lpp_stable_scaled_bound operation t)\<le>lpp_magnitude_max operation ts"
  by (induction ts) auto

lemma lpp_magnitude_max_le:
  "0\<le>M \<Longrightarrow> (\<And>t. t\<in>set ts \<Longrightarrow> abs (lpp_stable_scaled_bound operation t)\<le>M)
    \<Longrightarrow> lpp_magnitude_max operation ts\<le>M"
  by (induction ts) auto

definition lpp_magnitude_inputs where
  "lpp_magnitude_inputs j ts = take j ts @ drop (Suc j) ts"

lemma lpp_magnitude_inputs_map:
  "lpp_magnitude_inputs j (map f ts) = map f (lpp_magnitude_inputs j ts)"
  by (simp add: lpp_magnitude_inputs_def take_map drop_map)

definition lpp_magnitude_holds where
  "lpp_magnitude_holds operation summaries a = (\<forall>j\<in>set (summaries (fst a,length (snd a))).
    j<length (snd a) \<and> abs (lpp_stable_scaled_bound operation (snd a!j)) \<le>
      lpp_magnitude_max operation (lpp_magnitude_inputs j (snd a)))"

datatype 'v lpp_magnitude_fact =
  LPPMGEvaluate nat "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" lpp_magnitude_bound
| LPPMGModulo nat "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
    "(string lp_cut_symbol,'v) term" lpp_magnitude_bound
| LPPMGHelper nat nat "'v lpp_success_atom" "lpp_magnitude_bound list"

fun lpp_magnitude_conclusion where
  "lpp_magnitude_conclusion (LPPMGEvaluate i e r p) = r"
| "lpp_magnitude_conclusion (LPPMGModulo i a b r p) = r"
| "lpp_magnitude_conclusion (LPPMGHelper i j a ps) = snd a!j"

fun lpp_check_magnitude_fact where
  "lpp_check_magnitude_fact summaries bs gs known (LPPMGEvaluate i e r p) =
    (i<length gs \<and> gs!i=LPPSEvaluates e r \<and> lpp_check_magnitude_bound known e p)"
| "lpp_check_magnitude_fact summaries bs gs known (LPPMGModulo i a b r p) =
    (i<length gs \<and> gs!i=LPPSEvaluates (Fun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) r \<and>
      lpp_check_magnitude_bound known b p)"
| "lpp_check_magnitude_fact summaries bs gs known (LPPMGHelper i j a ps) =
    (i<length bs \<and> bs!i=a \<and> j<length (snd a) \<and> j\<in>set (summaries (fst a,length (snd a))) \<and>
      list_all2 (lpp_check_magnitude_bound known) (lpp_magnitude_inputs j (snd a)) ps)"

lemma lpp_check_magnitude_fact_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_magnitude_fact summaries bs gs known receipt"
    and known: "\<And>v. v\<in>set known \<Longrightarrow> abs (lpp_stable_scaled_bound operation (lp_ieval v eta))\<le>M"
    and nonnegative: "0\<le>M"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_magnitude_holds operation summaries (lpp_success_atom_eval b eta)) bs"
  shows "abs (lpp_stable_scaled_bound operation (lp_ieval (lpp_magnitude_conclusion receipt) eta))\<le>M"
proof (cases receipt)
  case (LPPMGEvaluate i e r p)
  have check: "lpp_check_magnitude_bound known e p" and index: "i<length gs"
    and equal: "gs!i=LPPSEvaluates e r"
    using checked by (simp_all add: LPPMGEvaluate)
  have member: "LPPSEvaluates e r\<in>set gs" using nth_mem[OF index] equal by simp
  have evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (lp_ieval r eta)"
    using guards member by (auto simp: list_all_iff)
  show ?thesis using lpp_check_magnitude_bound_sound[OF compatible check known nonnegative]
    lpp_stable_scaled_evaluation_value[OF evaluated] by (simp add: LPPMGEvaluate)
next
  case (LPPMGModulo i a b r p)
  have check: "lpp_check_magnitude_bound known b p" and index: "i<length gs"
    and equal: "gs!i=LPPSEvaluates (Fun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) r"
    using checked by (simp_all add: LPPMGModulo)
  have member: "LPPSEvaluates (Fun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) r\<in>set gs"
    using nth_mem[OF index] equal by simp
  have evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [lp_ieval a eta,lp_ieval b eta]) (lp_ieval r eta)"
    using guards member by (auto simp: list_all_iff)
  show ?thesis using lpp_check_magnitude_bound_sound[OF compatible check known nonnegative]
    lpp_stable_modulo_abs_bound[OF compatible evaluated] by (simp add: LPPMGModulo)
next
  case (LPPMGHelper i j a ps)
  have call_index: "i<length bs" and equal: "bs!i=a" and index: "j<length (snd a)"
    and selected: "j\<in>set (summaries (fst a,length (snd a)))"
    and checks: "list_all2 (lpp_check_magnitude_bound known) (lpp_magnitude_inputs j (snd a)) ps"
    using checked by (simp_all add: LPPMGHelper)
  have member: "a\<in>set bs" using nth_mem[OF call_index] equal by simp
  have held: "lpp_magnitude_holds operation summaries (lpp_success_atom_eval a eta)"
    using helpers member by (auto simp: list_all_iff)
  have bounded: "abs (lpp_stable_scaled_bound operation (lp_ieval t eta))\<le>M"
    if member_t: "t\<in>set (lpp_magnitude_inputs j (snd a))" for t
  proof -
    obtain p where check: "lpp_check_magnitude_bound known t p"
      using lpp_magnitude_list_all2_member[OF checks member_t] by blast
    show ?thesis by (rule lpp_check_magnitude_bound_sound[OF compatible check known nonnegative])
  qed
  have max_bound: "lpp_magnitude_max operation
      (map (\<lambda>t. lp_ieval t eta) (lpp_magnitude_inputs j (snd a)))\<le>M"
    by (rule lpp_magnitude_max_le[OF nonnegative]) (use bounded in auto)
  have bound: "abs (lpp_stable_scaled_bound operation (lp_ieval (snd a!j) eta))\<le>
      lpp_magnitude_max operation (map (\<lambda>t. lp_ieval t eta) (lpp_magnitude_inputs j (snd a)))"
    using held selected index by (auto simp: lpp_magnitude_holds_def lpp_success_atom_eval_def lpp_magnitude_inputs_map)
  show ?thesis using bound max_bound by (simp add: LPPMGHelper)
qed

fun lpp_check_magnitude_facts where
  "lpp_check_magnitude_facts summaries bs gs known [] = True"
| "lpp_check_magnitude_facts summaries bs gs known (f#fs) =
    (lpp_check_magnitude_fact summaries bs gs known f \<and>
     lpp_check_magnitude_facts summaries bs gs (known@[lpp_magnitude_conclusion f]) fs)"

lemma lpp_check_magnitude_facts_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_magnitude_facts summaries bs gs known facts"
    and known: "\<And>v. v\<in>set known \<Longrightarrow> abs (lpp_stable_scaled_bound operation (lp_ieval v eta))\<le>M"
    and nonnegative: "0\<le>M"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_magnitude_holds operation summaries (lpp_success_atom_eval b eta)) bs"
    and member: "t\<in>set (known@map lpp_magnitude_conclusion facts)"
  shows "abs (lpp_stable_scaled_bound operation (lp_ieval t eta))\<le>M"
  using checked known member
proof (induction facts arbitrary: known)
  case Nil then show ?case by simp
next
  case (Cons f fs)
  have current: "abs (lpp_stable_scaled_bound operation (lp_ieval (lpp_magnitude_conclusion f) eta))\<le>M"
    by (rule lpp_check_magnitude_fact_sound[OF compatible _ Cons.prems(2) nonnegative guards helpers])
      (use Cons.prems in auto)
  show ?case by (rule Cons.IH[where known="known@[lpp_magnitude_conclusion f]"])
    (use Cons.prems current in auto)
qed

ML \<open>
val checked = [@{thm lpp_check_magnitude_fact_sound}, @{thm lpp_check_magnitude_facts_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted magnitude fact dependency" else ();
\<close>
end
