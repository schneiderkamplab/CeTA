theory LP_Cut_Residual_Certificate
  imports LP_Cut_Residual LP_Residual_Signature
begin

text \<open>Certification boundary for an ordinary-LP child obligation. The
child checker can use its concrete signature, while the graph simulation
continues to use the cut source's tagged signature. This theorem does not
replace executable validation of the local graph obligations.\<close>

theorem lp_cut_encoded_residual_termination:
  assumes local: "\<And>i \<eta>.
      i \<in> I \<Longrightarrow> lp_cut_knowledge (set (G i)) (K i) \<eta> \<Longrightarrow>
      (\<And>j \<nu>. j \<in> I \<Longrightarrow>
        lp_cut_knowledge (set (G j)) (K j) \<nu> \<Longrightarrow>
        ([(F i,map \<eta> (V i))],[(F j,map \<nu> (V j))]) \<in> lp_ild Q \<Longrightarrow>
        SN_on (lp_cut_source P) {lp_cut_state_eval (N j) \<nu>}) \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
    and child: "SN_on (lp_ild (lp_signature_program encode Q))
      {map (lp_signature_iatom encode) qs}"
    and root: "i \<in> I" "lp_cut_knowledge (set (G i)) (K i) \<eta>"
      "qs = [(F i,map \<eta> (V i))]"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (N i) \<eta>}"
  by (rule lp_cut_recursive_residual_termination[where I=I and G=G and K=K
      and F=F and V=V and Q=Q and P=P and N=N and qs=qs and i=i and \<eta>=\<eta>,
      OF local lp_signature_termination_reflect[OF child] root])

end
