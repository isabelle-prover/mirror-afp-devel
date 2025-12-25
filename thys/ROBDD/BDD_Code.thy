section\<open>Code export\<close>
theory BDD_Code
imports Level_Collapse
begin

text\<open>For convenience reasons, the code export is in a separate theory. For Haskell, we only have to reactivate the original equation for @{term blit}. Other languages might need an implementation for it.\<close>

declare blit_def[code]

export_code open iteci_lu notci andci orci nandci norci biimpci xorci ifci tci fci tautci emptyci graphifyci litci eqci checking Haskell

end
