theory Relative_ADP_Integration_Base
  imports
    Relative_ADP_Checker_Dev.Relative_ADP_Checker_Adapter
    Proof_Checker.Ceta_Verifier
    RFC_Absolute_Ext.RFC_Absolute_Cert
begin

text \<open>Shared production imports are checked once in the parent session.
Parser and dispatch changes can then reuse that verified heap.\<close>

end
