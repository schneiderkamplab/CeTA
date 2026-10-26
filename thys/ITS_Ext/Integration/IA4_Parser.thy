theory IA4_Parser
  imports IA4_Instance LTS.LTS_Parser
begin

partial_function (sum_bot) ia4_exp_parser' :: "'a xmlt \<Rightarrow> 'a ia4_exp xmlt" where
  [code]: "ia4_exp_parser' v xml = (
  XMLdo (STR ''div'') {
    a \<leftarrow> ia4_exp_parser' v;
    d \<leftarrow> ia4_exp_parser' v;
    (if vars_term d \<noteq> {} then xml_error (STR ''symbolic div/mod divisor is unsupported'')
     else if divisor_value d = 0 then xml_error (STR ''zero div/mod divisor is unsupported'')
     else xml_return (Fun IA4_Div [a,d]))
  } XMLor   XMLdo (STR ''mod'') {
    a \<leftarrow> ia4_exp_parser' v;
    d \<leftarrow> ia4_exp_parser' v;
    (if vars_term d \<noteq> {} then xml_error (STR ''symbolic div/mod divisor is unsupported'')
     else if divisor_value d = 0 then xml_error (STR ''zero div/mod divisor is unsupported'')
     else xml_return (Fun IA4_Mod [a,d]))
  } XMLor   XMLdo (STR ''product'') {
    exps \<leftarrow>* ia4_exp_parser' v;
    xml_return (Fun (IA4_Base (IA.ProdF (length exps))) exps)
  } XMLor XMLdo (STR ''sum'') {
    exps \<leftarrow>* ia4_exp_parser' v;
    xml_return (Fun (IA4_Base (IA.SumF (length exps))) exps)
  } XMLor xml_change (xml_int (STR ''constant'')) (\<lambda>i. xml_return (Fun (IA4_Base (IA.ConstF i)) []))
  XMLor xml_change v (\<lambda> x. xml_return (Var (x,IA.IntT)))
  ) xml"

definition ia4_bexp_parser' :: "'a xmlt \<Rightarrow> 'a ia4_exp formula xmlt" where
 "ia4_bexp_parser' v \<equiv>
  (let ia4_bexp_parser'' =
  XMLdo (STR ''leq'') {
    l \<leftarrow> ia4_exp_parser' v;
    r \<leftarrow> ia4_exp_parser' v;
    xml_return (Fun (IA4_Base IA.LeF) [l, r])
  } XMLor XMLdo (STR ''less'') {
    l \<leftarrow> ia4_exp_parser' v;
    r \<leftarrow> ia4_exp_parser' v;
    xml_return (Fun (IA4_Base IA.LessF) [l,r])
  } XMLor XMLdo (STR ''eq'') {
    l \<leftarrow> ia4_exp_parser' v;
    r \<leftarrow> ia4_exp_parser' v;
    xml_return (Fun (IA4_Base IA.EqF) [l,r])
  } XMLor XMLdo (STR ''geq'') {
    l \<leftarrow> ia4_exp_parser' v;
    r \<leftarrow> ia4_exp_parser' v;
    xml_return (Fun (IA4_Base IA.LeF) [r,l])
  } XMLor XMLdo (STR ''greater'') {
    l \<leftarrow> ia4_exp_parser' v;
    r \<leftarrow> ia4_exp_parser' v;
    xml_return (Fun (IA4_Base IA.LessF) [r,l])
  }
  in
  XMLdo STR ''not'' {a \<leftarrow> ia4_bexp_parser''; xml_return (NegAtom a)}
  XMLor xml_change ia4_bexp_parser'' (xml_return \<circ> Atom))"

definition "ia4_exp_parser \<equiv> ia4_exp_parser' variable_parser"
definition "ia4_atom_parser \<equiv> xml_change (ia4_bexp_parser' variable_parser) xml_return"
definition "ia4_tatom_parser \<equiv> xml_change (ia4_bexp_parser' trans_var_parser) xml_return"
definition "ia4_atom_parser' = xml_change (ia4_bexp_parser' variable_parser) xml_return"
definition "ia4_tatom_parser' = xml_change (ia4_bexp_parser' trans_var_parser) xml_return"


definition "ia4_lts_input_parser \<equiv>
  lts_parser (location_parser xml_text) (trans_id xml_text) ia4_tatom_parser (STR ''lts'')"
definition "ia4_lts_termination_proof_parser \<equiv>
  termination_proof_parser xml_text xml_text ia4_exp_parser ia4_atom_parser ia4_tatom_parser
    variable_parser type_parser IA.IntT"

end
