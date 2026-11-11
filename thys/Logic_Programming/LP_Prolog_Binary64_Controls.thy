theory LP_Prolog_Binary64_Controls
 imports LP_Prolog_Binary64_Evaluation
begin

text \<open>Executable regression checks, not proof axioms or replacement proofs.
The general rounding and evaluation soundness theorems are checked independently.\<close>

ML \<open>
val controls = [
@{term "lpp_binary64_round_fraction False 9007199254740993 1=Some 4845873199050653696"},
@{term "lpp_binary64_round_fraction False 9007199254740995 1=Some 4845873199050653698"},
@{term "lpp_binary64_round_fraction False 9007199254740991 1=Some 4845873199050653695"},
@{term "lpp_binary64_round_fraction False 18014398509481983 1=Some 4850376798678024192"},
@{term "lpp_binary64_round_fraction False 18014398509481985 1=Some 4850376798678024192"},
@{term "lpp_binary64_round_fraction False 1 (2^1074)=Some 1"},
@{term "lpp_binary64_round_fraction False 1 (2^1075)=Some 0"},
@{term "lpp_binary64_round_fraction False 3 (2^1075)=Some 2"},
@{term "lpp_binary64_round_fraction False (-1) (2^1075)=Some (2^63)"},
@{term "lpp_binary64_round_fraction False ((2^53-1)*2^971) 1=Some 9218868437227405311"},
@{term "lpp_binary64_round_fraction False (2^1024-2^970) 1=None"},
@{term "lpp_binary64_round_fraction False 1 0=None"},
@{term "lpp_machine_binary ''2:prolog_data_2d'' (LPPMachineInteger 9007199254740993)
   (LPPMachineFloat 4845873199050653696)=Some (LPPMachineFloat 0)"},
@{term "lpp_machine_binary ''2:prolog_data_2b'' (LPPMachineFloat (2^63))
   (LPPMachineFloat (2^63))=Some (LPPMachineFloat (2^63))"},
@{term "lpp_machine_binary ''2:prolog_data_2d'' (LPPMachineFloat (2^63))
   (LPPMachineFloat 0)=Some (LPPMachineFloat (2^63))"},
@{term "lpp_machine_binary ''2:prolog_data_2a'' (LPPMachineFloat 0)
   (LPPMachineInteger (-1))=Some (LPPMachineFloat (2^63))"}];
val _ = List.app (fn t =>
  if Code_Evaluation.dynamic_value_strict @{context} t aconv @{term True} then ()
  else error ("Binary64 executable control failed: " ^ Syntax.string_of_term @{context} t)) controls;
val _ = writeln ("BINARY64_RUNTIME_CONTROLS_PASSED " ^ string_of_int (length controls));
\<close>
end
