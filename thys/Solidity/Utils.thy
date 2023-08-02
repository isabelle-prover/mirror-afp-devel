theory Utils
imports
  Main
  "HOL-Eisbach.Eisbach"
begin

method solve methods m = (m ; fail)

named_theorems intros
declare conjI[intros] impI[intros] allI[intros]
method intros = (rule intros; intros?)

named_theorems elims
method elims = ((rule intros | erule elims); elims?)
declare conjE[elims]

end