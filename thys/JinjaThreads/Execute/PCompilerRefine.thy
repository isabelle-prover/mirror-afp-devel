theory PCompilerRefine imports
  "TypeRelRefine"
  "../Compiler/PCompiler"
begin

subsection {* @{term "compP"} *}

text {* 
  Although it is possible to adapt the compiler framework to work with tabulated programs, 
  it is not sensible to apply the compiler to the tabulated program because this requires
  either to compile every method twice (once for the program itself and once for method lookup)
  or to recompute the class and method lookup tabulation from scratch.
  We follow the second approach.
*}

fun compP_code' :: "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a prog_impl' \<Rightarrow> 'b prog_impl'"
where
  "compP_code' f (P, Cs, s, F, m) = 
  (let P' = map (compC f) P
   in (P', tabulate_class P', s, F, tabulate_Method P'))"

definition compP_code :: "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a prog_impl \<Rightarrow> 'b prog_impl"
where "compP_code f P = ProgRefine (compP_code' f (impl_of P))"

declare compP.simps [simp del] compP.simps[symmetric, simp]

lemma compP_code_code [code abstract]:
  "impl_of (compP_code f P) = compP_code' f (impl_of P)"
apply(cases P)
apply(simp add: compP_code_def)
apply(subst ProgRefine_inverse)
apply(auto)

apply(simp add: tabulate_subcls_def cong: if_cong)

apply(fastsimp simp add: tabulate_sees_field_def intro!: ext)
done

declare compP.simps [simp] compP.simps[symmetric, simp del]

lemma compP_program [code]:
  "compP f (program P) = program (compP_code f P)"
by(cases P)(clarsimp simp add: program_def compP_code_code)

text {* Merge module names to avoid cycles in module dependency *}

code_modulename SML
  PCompiler PCompiler
  PCompilerRefine PCompiler

code_modulename OCaml
  PCompiler PCompiler
  PCompilerRefine PCompiler

code_modulename Haskell
  PCompiler PCompiler
  PCompilerRefine PCompiler

ML {* @{code compP} *}

end