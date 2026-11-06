theory LP_Prolog_Stable_Fuel_Evaluation
  imports LP_Prolog_Stable_Integer_Compatibility
begin

text \<open>This evaluator accounts for one shared budget across both operands.
An exhausted budget produces no successful observation; it is not a proof of
finite source failure. The operation parameter is fixed by the source profile,
not supplied by a certificate. Scalar recognition is stated semantically here;
this function is not a replacement for the native arithmetic implementation.\<close>

fun lpp_stable_fuel_evaluate ::
  "(string lp_cut_symbol \<Rightarrow> (string lp_cut_symbol,'v) lp_iterm list \<Rightarrow>
    (string lp_cut_symbol,'v) lp_iterm option) \<Rightarrow> nat \<Rightarrow>
    (string lp_cut_symbol,'v) lp_iterm \<Rightarrow>
    ((string lp_cut_symbol,'v) lp_iterm \<times> nat) option" where
  "lpp_stable_fuel_evaluate operation 0 expression = None"
| "lpp_stable_fuel_evaluate operation (Suc fuel) (LPIFun f []) =
    (if \<exists>n d. lpp_scalar_fraction (LPIFun f [] :: (string lp_cut_symbol,'v) lp_iterm) n d
     then Some (LPIFun f [], fuel) else None)"
| "lpp_stable_fuel_evaluate operation (Suc fuel) (LPIFun f [a]) =
    (case lpp_stable_fuel_evaluate operation fuel a of None \<Rightarrow> None
     | Some (x, rest) \<Rightarrow> (case operation f [x] of None \<Rightarrow> None
       | Some v \<Rightarrow> (if \<exists>n d. lpp_scalar_fraction v n d
          then Some (v, rest) else None)))"
| "lpp_stable_fuel_evaluate operation (Suc fuel) (LPIFun f [a,b]) =
    (case lpp_stable_fuel_evaluate operation fuel a of None \<Rightarrow> None
     | Some (x, rest) \<Rightarrow>
       (if rest > fuel then None else case lpp_stable_fuel_evaluate operation rest b of None \<Rightarrow> None
        | Some (y, final) \<Rightarrow> (case operation f [x,y] of None \<Rightarrow> None
          | Some v \<Rightarrow> (if \<exists>n d. lpp_scalar_fraction v n d
             then Some (v, final) else None))))"
| "lpp_stable_fuel_evaluate operation (Suc fuel) expression = None"

lemma lpp_stable_fuel_evaluate_sound:
  "lpp_stable_fuel_evaluate operation fuel expression = Some (v, rest) \<Longrightarrow>
   lpp_stable_scalar_evaluation operation expression v"
proof (induction operation fuel expression arbitrary: v rest
    rule: lpp_stable_fuel_evaluate.induct)
  case (4 operation fuel f a b)
  obtain x r y where first:
      "lpp_stable_fuel_evaluate operation fuel a = Some (x, r)"
    and budget: "\<not> fuel < r"
    and second: "lpp_stable_fuel_evaluate operation r b = Some (y, rest)"
    and applied: "operation f [x,y] = Some v"
    and scalar: "\<exists>n d. lpp_scalar_fraction v n d"
    using "4.prems" by (auto split: option.splits prod.splits if_splits)
  have left: "lpp_stable_scalar_evaluation operation a x"
    by (rule "4.IH"(1)[OF first])
  have right: "lpp_stable_scalar_evaluation operation b y"
    by (rule "4.IH"(2)[OF first refl budget second])
  show ?case using left right applied scalar
    by (blast intro: lpp_stable_scalar_evaluation.binary)
qed (auto split: option.splits prod.splits if_splits
  intro: lpp_stable_scalar_evaluation.intros)

lemma lpp_stable_fuel_remaining:
  "lpp_stable_fuel_evaluate operation fuel expression = Some (v, rest) \<Longrightarrow>
   rest < fuel"
proof (induction operation fuel expression arbitrary: v rest
    rule: lpp_stable_fuel_evaluate.induct)
  case (4 operation fuel f a b)
  obtain x r y where first:
      "lpp_stable_fuel_evaluate operation fuel a = Some (x, r)"
    and budget: "\<not> fuel < r"
    and second: "lpp_stable_fuel_evaluate operation r b = Some (y, rest)"
    using "4.prems" by (auto split: option.splits prod.splits if_splits)
  have "rest < r" by (rule "4.IH"(2)[OF first refl budget second])
  then show ?case using budget by arith
qed (auto split: option.splits prod.splits if_splits)

lemma lpp_stable_fuel_result_independent:
  assumes "lpp_stable_fuel_evaluate operation fuel expression = Some (v, rest)"
    "lpp_stable_fuel_evaluate operation other_fuel expression = Some (w, other_rest)"
  shows "v = w"
  using assms lpp_stable_fuel_evaluate_sound
    lpp_stable_scalar_evaluation_unique by blast

ML \<open>
val checked = [@{thm lpp_stable_fuel_evaluate_sound},
  @{thm lpp_stable_fuel_result_independent}, @{thm lpp_stable_fuel_remaining}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted shared-budget arithmetic evaluation dependency" else ();
\<close>
end
