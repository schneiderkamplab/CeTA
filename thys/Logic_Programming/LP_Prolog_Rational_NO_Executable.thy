theory LP_Prolog_Rational_NO_Executable
  imports LP_Prolog_Rational_NO_XML
begin

declare lp_rational_match.simps[code del]
lemma lp_rational_match_code[code]:
  "lp_rational_match fuel G env t i =
    (if fuel=0 then False else i<length G \<and> (case t of
      Var x \<Rightarrow> map_of env x=Some i
    | Fun f ts \<Rightarrow> (case G!i of LPRExternal x \<Rightarrow> False
      | LPRBranch g js \<Rightarrow> f=g \<and> length ts=length js \<and>
        list_all (\<lambda>k. lp_rational_match (fuel-1) G env (ts!k) (js!k)) [0..<length ts])))"
  by (cases fuel; cases t) (auto simp: diff_Suc_1 split: lp_rational_node.splits)

declare lp_rational_distinct.simps[code del]
lemma lp_rational_distinct_code[code]:
  "lp_rational_distinct fuel G i j =
    (if fuel=0 then False else i<length G \<and> j<length G \<and>
      (case (G!i,G!j) of (LPRBranch f xs,LPRBranch g ys) \<Rightarrow>
        f\<noteq>g \<or> length xs\<noteq>length ys \<or>
          list_ex (\<lambda>k. lp_rational_distinct (fuel-1) G (xs!k) (ys!k)) [0..<min (length xs) (length ys)]
      | _ \<Rightarrow> False))"
  by (cases fuel) (auto simp: diff_Suc_1 split: lp_rational_node.splits)
end
