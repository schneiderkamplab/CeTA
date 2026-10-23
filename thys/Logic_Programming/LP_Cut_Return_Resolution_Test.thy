theory LP_Cut_Return_Resolution_Test
  imports LP_Cut_Return_Resolution
begin

lemma normalized_answer_positive:
  "lpc_check_return_values 30 2 [] [(Var ''$$x'',Fun (LPCUser ''z'') [])]
    [Var ''x''] [Var ''x''] [Fun (LPCUser ''z'') []]"
  by eval

lemma forged_answer_rejected:
  "\<not>lpc_check_return_values 30 2 [] [(Var ''$$x'',Fun (LPCUser ''z'') [])]
    [Var ''x''] [Var ''x''] [Fun (LPCUser ''wrong'') []]"
  by eval

lemma omitted_answer_rejected:
  "\<not>lpc_check_return_values 30 2 [] [(Var ''$$x'',Fun (LPCUser ''z'') [])]
    [Var ''x''] [Var ''x''] []"
  by eval

lemma stale_answer_rejected:
  "\<not>lpc_check_return_values 30 2 [] [(Var ''$$x'',Fun (LPCUser ''z'') [])]
    [Var ''x''] [Var ''x''] [Var ''x'']"
  by eval

lemma answer_only_freshness_required:
  "\<not>lpc_check_return_values 30 2 [] [(Var ''$$x'',Fun (LPCUser ''z'') [])]
    [Var ''x''] [Var ''$$x''] [Fun (LPCUser ''z'') []]"
  by eval

end
