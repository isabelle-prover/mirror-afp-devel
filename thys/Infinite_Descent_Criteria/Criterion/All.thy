(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsection "All Criterion"
theory All imports

Flat_Cycles_Criterion
Descending_Unicycles_Criterion
Incomplete_Criteria
SLA_Criterion
VLA_Criterion
Relation_Based_Criterion

begin


context Sloped_Graph
begin
thm Flat_Cycles_Criterion
    DescendingUnicyclesCriterion
    Incomplete_Criterion
    SLA_Criterion 
    VLA_Criterion 
    Relation_Based_Criterion
    Relation_Based_Criterion'
   
end
end