theory Generate_Binary_Nat
imports
  "Candidates"
  "HOL-Library.AList_Mapping"
  "HOL-Library.Finite_Lattice"
  "HOL-Library.Code_Binary_Nat"
  "Go.Go_Setup"
begin



export_code _ checking Go? (infinite_type "stream")

end
