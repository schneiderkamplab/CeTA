theory Higher_Order_Code
  imports Higher_Order_Plain_Path
begin

lemma ho_rule_welltyped_spec:
  "ho_rule_welltyped S (G,l,r) \<longleftrightarrow>
    (\<exists>A. ho_typeof S G [] (ho_erase_pattern l) = Some A \<and>
      ho_typeof S G [] (ho_erase_pattern r) = Some A)"
  by (auto simp: ho_rule_welltyped_def split: option.splits)

text \<open>The exported checker accepts only a nonempty, typed closed cycle.
An empty derivation or an ill-typed endpoint is not nontermination evidence.\<close>

lemma reject_empty_loop: "\<not> ho_check_loop S V R A t []"
  by (simp add: ho_check_loop_def)

lemma reject_untyped_loop:
  "ho_typeof S V [] t \<noteq> Some A \<Longrightarrow> \<not> ho_check_loop S V R A t ps"
  by (cases ps) (auto simp: ho_check_loop_def split: option.splits)

export_code ho_check_loop ho_check_embedding ho_check_rule_pump ho_check_plain_pump ho_check_step ho_typeof nat_of_integer
  HBase HArrow HBound HFree HConst HApp HAbs PBound PConst PApp PAbs PMeta
  HRule HBeta HLeft HRight HUnder
  HHole HCLeft HCRight
  in Haskell module_name Higher_Order_Checker

end
