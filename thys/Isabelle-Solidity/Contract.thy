theory Contract
  imports Solidity WP
  keywords "contract" :: thy_decl
       and "constructor"
       and "cfunction"
       and "external"
       and "memory"
       and "param"
       and "calldata"
       and "payable"
       and "verification" :: thy_goal
       and "invariant"::thy_decl

begin
ML_file Utils.ML
ML_file Data.ML
ML_file Specification.ML
ML_file Invariant.ML
ML_file Verification.ML

end
