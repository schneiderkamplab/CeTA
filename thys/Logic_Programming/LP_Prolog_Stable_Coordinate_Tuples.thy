theory LP_Prolog_Stable_Coordinate_Tuples
 imports LP_Prolog_Stable_Coordinate_Controls
begin

lemma lpp_stable_numeric_tuple_Nil[simp]:
  "lpp_stable_numeric_tuple operation [] [] [] rho"
  by (simp add: lpp_stable_numeric_tuple_def)

lemma lpp_stable_numeric_tuple_Cons:
  "lpp_stable_numeric_tuple operation (x#xs) (mode#modes) (t#ts) rho =
    (lpp_stable_coordinate_value operation mode t (rho x) \<and>
      lpp_stable_numeric_tuple operation xs modes ts rho)"
  by (auto simp: lpp_stable_numeric_tuple_def less_Suc_eq_0_disj)

lemma lpp_stable_numeric_tuple_coordinates:
  assumes tuple: "lpp_stable_numeric_tuple operation names modes ts rho"
    and equal: "\<And>x. x\<in>set names \<Longrightarrow> rho' x=rho x"
  shows "lpp_stable_numeric_tuple operation names modes ts rho'"
  using tuple equal by (auto simp: lpp_stable_numeric_tuple_def)

lemma lpp_stable_numeric_tuple_exists:
  assumes names: "distinct names" and len: "length names=length ts"
    and typed: "list_all2 (\<lambda>mode t. \<exists>k. lpp_stable_coordinate_value operation mode t k) modes ts"
  shows "\<exists>rho. lpp_stable_numeric_tuple operation names modes ts rho"
  using names len typed
proof (induct names arbitrary: modes ts)
  case Nil then show ?case by (auto simp: list_all2_Nil2)
next
  case (Cons x xs)
  obtain t us where ts: "ts=t#us" using Cons.prems by (cases ts) auto
  obtain mode rest where modes: "modes=mode#rest"
    and current: "\<exists>k. lpp_stable_coordinate_value operation mode t k"
    and tail: "list_all2 (\<lambda>mode t. \<exists>k. lpp_stable_coordinate_value operation mode t k) rest us"
    using Cons.prems ts by (cases modes) auto
  obtain k where coordinate_value: "lpp_stable_coordinate_value operation mode t k" using current by blast
  obtain rho where child: "lpp_stable_numeric_tuple operation xs rest us rho"
    using Cons.hyps Cons.prems ts tail by auto
  have changed: "lpp_stable_numeric_tuple operation xs rest us (rho(x:=k))"
    by (rule lpp_stable_numeric_tuple_coordinates[OF child]) (use Cons.prems in auto)
  have "lpp_stable_numeric_tuple operation (x#xs) modes ts (rho(x:=k))"
    using coordinate_value changed by (simp add: modes ts lpp_stable_numeric_tuple_Cons)
  then show ?case by blast
qed

ML \<open>
val checked = [@{thm lpp_stable_numeric_tuple_exists}, @{thm lpp_stable_numeric_tuple_coordinates}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable coordinate tuple dependency" else ();
\<close>
end
