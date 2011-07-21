theory Compiler imports Compiler1 Compiler2 begin

definition J2JVM :: "'addr J_prog \<Rightarrow> 'addr jvm_prog"
where "J2JVM \<equiv> compP2 \<circ> compP1"

end