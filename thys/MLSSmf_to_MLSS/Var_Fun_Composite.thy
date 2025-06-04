theory Var_Fun_Composite
  imports Main
begin          

text \<open>
  A compositional type for the reduction algorithm,
  to ensure uniqueness of variables in the generated MLSS formulae
\<close>

datatype ('v, 'f) Composite =
  Solo 'v |
  VennRegion "'v set" (\<open>v\<^bsub>_\<^esub>\<close>) |
  FunOfUnionOfVennRegions 'f "'v set set" (\<open>w\<^bsub>_\<^esub>\<^bsub>_\<^esub>\<close>) |
  InterOfWAux 'f "'v set set" "'v set set" |
  UnionOfVars "'v list" |
  InterOfVarsAux "'v list" |
  InterOfVars "'v list" |
  UnionOfVennRegions "'v set list" |
  MemAux 'v

end