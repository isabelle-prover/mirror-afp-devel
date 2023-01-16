(*  Title:       A Reuse-Based Multi-Stage Compiler Verification for Language IMP
    Author:      Pasquale Noce
                 Senior Staff Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Compiler formalization"

theory Compiler
  imports
    "HOL-IMP.Big_Step"
    "HOL-IMP.Star"
begin

text \<open>
\null

\emph{This paper is dedicated to Gaia and Greta, my sweet nieces, who fill my life with love and
happiness.}

\null\null

After introducing the didactic imperative programming language IMP, \<^cite>\<open>"Nipkow21-1"\<close> specifies
compilation of IMP commands into a lower-level language based on a stack machine, and expounds a
formal verification of that compiler. Exercise 8.4 asks the reader to adjust such proof for a new
compilation target, consisting of a machine language that (i) accesses memory locations through
their addresses instead of variable names, and (ii) maintains a stack in memory via a stack pointer
rather than relying upon a built-in stack. A natural strategy to maximize reuse of the original
proof is keeping the original language as an assembly one and splitting compilation into multiple
steps, namely a source-to-assembly step matching the original compilation process followed by an
assembly-to-machine step. In this way, proving assembly code-machine code equivalence is the only
extant task.

\<^cite>\<open>"Noce21"\<close> introduces a reasoning toolbox that allows for a compiler correctness proof shorter
than the book's one, as such promising to constitute a further enhanced reference for the formal
verification of real-world compilers. This paper in turn shows that such toolbox can be reused to
accomplish the aforesaid task as well, which demonstrates that the proposed approach also promotes
proof reuse in multi-stage compiler verifications.

The formal proof development presented in this paper consists of two theory files, as follows.

  \<^item> The former theory, briefly referred to as ``the @{text Compiler} theory'', is derived from the
@{text "HOL-IMP.Compiler"} one included in the Isabelle2021-1 distribution \<^cite>\<open>"Nipkow21-2"\<close>.\\
However, the signature of function @{text bcomp} is modified in the same way as in \<^cite>\<open>"Noce21"\<close>.

  \<^item> The latter theory, briefly referred to as ``the @{text Compiler2} theory'', is derived from the
@{text Compiler2} one developed in \<^cite>\<open>"Noce21"\<close>.\\
However, unlike \<^cite>\<open>"Noce21"\<close>, the original language IMP is considered here, without extending it
with non-deterministic choice. Hence, the additional case pertaining to non-deterministic choice in
the proof of lemma @{text ccomp_correct} is not present any longer.

Both theory files are split into the same subsections as the respective original theories, and only
the most salient differences with respect to the original theories are commented in both of them.

For further information about the formal definitions and proofs contained in this paper, see
Isabelle documentation, particularly \<^cite>\<open>"Paulson21"\<close>, \<^cite>\<open>"Nipkow21-3"\<close>, \<^cite>\<open>"Krauss21"\<close>,
and \<^cite>\<open>"Nipkow11"\<close>.
\<close>


subsection "List setup"

declare [[coercion_enabled]]
declare [[coercion "int :: nat \<Rightarrow> int"]]
declare [[syntax_ambiguity_warning = false]]

abbreviation (output)
"isize xs \<equiv> int (length xs)"

notation isize ("size")

primrec (nonexhaustive) inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

lemma inth_append [simp]:
 "0 \<le> i \<Longrightarrow>
    (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i, auto simp: algebra_simps)


subsection "Instructions and stack machine"

text \<open>
Here below, both the syntax and the semantics of the instruction set are defined. As a deterministic
language is considered here, as opposed to the non-deterministic one addressed in \<^cite>\<open>"Noce21"\<close>,
instruction semantics can be defined via a simple non-recursive function @{text iexec} (identical to
the one used in \<^cite>\<open>"Nipkow21-1"\<close>, since the instruction set is the same). However, an inductive
predicate @{text iexec_pred}, resembling the @{text iexec} one used in \<^cite>\<open>"Noce21"\<close> and denoted
by the same infix symbol @{text \<mapsto>}, is also defined. Though notation @{text "(ins, cf) \<mapsto> cf'"} is
just an alias for @{text "cf' = iexec ins cf"}, it is used in place of the latter in the definition
of predicate @{text exec1}, which formalizes single-step program execution. The reason is that the
compiler correctness proof developed in the @{text Compiler2} theory of \<^cite>\<open>"Noce21"\<close> depends on
the introduction and elimination rules deriving from predicate @{text iexec}'s inductive definition.
Thus, the use of predicate @{text iexec_pred} is a trick enabling Isabelle's classical reasoner to
keep using such rules, which restricts the changes to be made to the proofs in the @{text Compiler2}
theory to those required by the change of the compilation target.

The instructions defined by type @{text instr}, which refer to memory locations via variable names,
will keep being used as an assembly language. In order to have a machine language rather referring
to memory locations via their addresses, modeled as integers, an additional type @{text m_instr} of
machine instructions, in one-to-one correspondence with assembly instructions, is introduced. The
underlying idea is to reuse the proofs that source code and compiled (assembly) code simulate each
other built in \<^cite>\<open>"Nipkow21-2"\<close> and \<^cite>\<open>"Noce21"\<close>, so that the only extant task is proving
that assembly code and machine code in turn simulate each other. This is nothing but an application
of the \emph{divide et impera} strategy of considering multiple compilation stages mentioned in
\<^cite>\<open>"Nipkow21-1"\<close>, section 8.5.

In other words, the solution developed in what follows does not require any change to the original
compiler completeness and correctness proofs. This result is achieved by splitting compilation into
multiple steps, namely a source-to-assembly step matching the original compilation process, to which
the aforesaid proofs still apply, followed by an assembly-to-machine step. In this way, to establish
source code-machine code equivalence, the assembly code-machine code one is all that is left to be
proven. In addition to proof reuse, this approach provides the following further advantages.

  \<^item> There is no need to reason about the composition and decomposition of machine code sequences,
    which would also involve the composition and decomposition of the respective mappings between
    used variables and their addresses (as opposed to what happens with assembly code sequences).

  \<^item> There is no need to change the original compilation functions, modeling the source-to-assembly
    compilation step in the current context. In fact, the outputs of these functions are assembly
    programs, namely lists of assembly instructions, which are in one-to-one correspondence with
    machine ones. Thus, the assembly-to-machine compilation step can easily be modeled as a mapping
    of such a list into a machine instruction one, where each referenced variable can be assigned an
    unambiguous address based on the position of the first/last instruction referencing it within
    the assembly program.

\null
\<close>

datatype instr = 
  LOADI int | LOAD vname | ADD | STORE vname |
  JMP int | JMPLESS int | JMPGE int

type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs \<equiv> hd (tl xs)"
abbreviation "tl2 xs \<equiv> tl (tl xs)"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
"iexec ins (i, s, stk) = (case ins of
  LOADI n \<Rightarrow> (i + 1, s, n # stk) |
  LOAD x \<Rightarrow> (i + 1, s, s x # stk) |
  ADD \<Rightarrow> (i + 1, s, (hd2 stk + hd stk) # tl2 stk) |
  STORE x \<Rightarrow> (i + 1, s(x := hd stk), tl stk) |
  JMP n \<Rightarrow> (i + 1 + n, s, stk) |
  JMPLESS n \<Rightarrow> (if hd2 stk < hd stk then i + 1 + n else i + 1, s, tl2 stk) |
  JMPGE n \<Rightarrow> (if hd2 stk \<ge> hd stk then i + 1 + n else i + 1, s, tl2 stk))"

inductive iexec_pred :: "instr \<times> config \<Rightarrow> config \<Rightarrow> bool"
  (infix "\<mapsto>" 55) where
"(ins, cf) \<mapsto> iexec ins cf"

definition exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile>/ _/ \<rightarrow>/ _)" 55) where
"P \<turnstile> cf \<rightarrow> cf' \<equiv> (P !! fst cf, cf) \<mapsto> cf' \<and> 0 \<le> fst cf \<and> fst cf < size P"

abbreviation exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile>/ _/ \<rightarrow>*/ _)" 55) where
"exec P \<equiv> star (exec1 P)"


declare iexec_pred.intros [intro]

inductive_cases LoadIE  [elim!]:  "(LOADI i, pc, s, stk) \<mapsto> cf"
inductive_cases LoadE  [elim!]:  "(LOAD x, pc, s, stk) \<mapsto> cf"
inductive_cases AddE  [elim!]:  "(ADD, pc, s, stk) \<mapsto> cf"
inductive_cases StoreE  [elim!]:  "(STORE x, pc, s, stk) \<mapsto> cf"
inductive_cases JmpE  [elim!]:  "(JMP i, pc, s, stk) \<mapsto> cf"
inductive_cases JmpLessE  [elim!]:  "(JMPLESS i, pc, s, stk) \<mapsto> cf"
inductive_cases JmpGeE  [elim!]:  "(JMPGE i, pc, s, stk) \<mapsto> cf"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

lemma iexec_simp:
 "(ins, cf) \<mapsto> cf' = (cf' = iexec ins cf)"
by (auto elim: iexec_pred.cases)

lemma exec1I [intro, code_pred_intro]:
 "\<lbrakk>c' = iexec (P !! i) (i, s, stk); 0 \<le> i; i < size P\<rbrakk> \<Longrightarrow>
    P \<turnstile> (i, s, stk) \<rightarrow> c'"
by (auto simp: exec1_def iexec_simp)


type_synonym addr = int

datatype m_instr =
  M_LOADI int | M_LOAD addr | M_ADD | M_STORE addr |
  M_JMP int | M_JMPLESS int | M_JMPGE int

text \<open>
\null

Here below are the recursive definitions of functions @{text vars}, which takes an assembly program
as input and returns a list without repetitions of the referenced variables, and @{text addr_of},
which in turn takes a list of variables @{text xs} and a variable @{text x} as inputs and returns
the address @{text a} of @{text x}. If @{text x} is included in @{text xs}, @{text a} is set to the
one-based right offset of the leftmost occurrence of @{text x} in @{text xs}, otherwise @{text a} is
set to zero.

Therefore, for any assembly program @{text P}, function @{term "addr_of (vars P) :: vname \<Rightarrow> addr"}
maps each variable occurring within @{text P} to a distinct positive address, and any other, unused
variable to a default, invalid address (zero).

\null
\<close>

primrec vars :: "instr list \<Rightarrow> vname list" where
"vars [] = []" |
"vars (ins # P) = (case ins of
  LOAD x \<Rightarrow> if x \<in> set (vars P) then [] else [x] |
  STORE x \<Rightarrow> if x \<in> set (vars P) then [] else [x] |
  _ \<Rightarrow> []) @ vars P"

primrec addr_of :: "vname list \<Rightarrow> vname \<Rightarrow> addr" where
"addr_of [] _ = 0" |
"addr_of (x # xs) y = (if x = y then size xs + 1 else addr_of xs y)"

text \<open>
\null

Functions @{const vars} and @{const addr_of} can be used to translate an assembly program into a
machine program, which is done by the subsequent functions @{text to_m_instr} and @{text to_m_prog}.
The former takes a list of variables @{text xs} and an assembly instruction @{text ins} as inputs
and returns the corresponding machine instruction, which refers to address @{term "addr_of xs x"}
whenever @{text ins} references variable @{text x}. Then, the latter function turns each instruction
contained in the input assembly program @{text P} into the corresponding machine one, using function
@{term "to_m_instr (vars P) :: instr \<Rightarrow> m_instr"} for such mapping. Hence, each variable @{text x}
occurring within @{text P} is turned into the address @{term "addr_of (vars P) x"}, as expected.

In addition, the types @{text m_state} and @{text m_config} of machine states and configurations are
also defined here below. The former one encompasses any function mapping addresses to values. The
latter one reflects the fact that the third element of a machine configuration has to be a pointer
to a stack maintained by the machine state, rather than a list-encoded stack as keeps happening with
assembly configurations. This can be achieved using a natural number @{text sp} as third element,
standing for the current size of the machine stack. Hence, if it is nonempty, the address of its
topmost element matches $-sp$, given that the machine stack will be modeled by making it start from
address $-1$ and grow downward.

\null
\<close>

fun to_m_instr :: "vname list \<Rightarrow> instr \<Rightarrow> m_instr" where
"to_m_instr xs ins = (case ins of
  LOADI n \<Rightarrow> M_LOADI n |
  LOAD x \<Rightarrow> M_LOAD (addr_of xs x) |
  ADD \<Rightarrow> M_ADD |
  STORE x \<Rightarrow> M_STORE (addr_of xs x) |
  JMP n \<Rightarrow> M_JMP n |
  JMPLESS n \<Rightarrow> M_JMPLESS n |
  JMPGE n \<Rightarrow> M_JMPGE n)"

fun to_m_prog :: "instr list \<Rightarrow> m_instr list" where
"to_m_prog P = map (to_m_instr (vars P)) P"

type_synonym m_state = "addr \<Rightarrow> val"
type_synonym m_config = "int \<times> m_state \<times> nat"

text \<open>
\null

Next are the definitions of functions @{text to_state} and @{text to_m_state}, which turn a machine
program state @{text ms} into an equivalent assembly program state @{text s} and vice versa, based
on an input list of variables @{text xs}. Here, \emph{equivalent} means that for each variable
@{text x} in @{text xs}, @{text s} assigns @{text x} the same value that @{text ms} assigns to
@{text x}'s address @{term "addr_of xs x"}.

Function @{text "to_m_state xs s"} maps any positive address @{text a} up to @{term "size xs"} to
value @{term "s x"}, where @{text x} is the variable occurring within @{text xs} at the zero-based
left offset @{term "size xs - a"}, and any other, unused address to a default, dummy value (zero).
The resulting machine program state is equivalent to @{text s} since the zero-based left offset
@{term "size xs - a"} points to the same variable @{text x} within @{text xs} as the one-based right
offset @{text a}. As long as @{text xs} does not contain any repetition, as happens with the outputs
of function @{const vars}, @{text x} is indeed the variable such that @{prop "addr_of xs x = a"}, by
virtue of the definition of function @{const addr_of}. To perform the reverse conversion, function
@{text "to_state xs ms"} merely needs to map any variable @{text x} to @{term "ms (addr_of xs x)"}.

Hence, for any assembly program @{text P}, function @{term "to_state (vars P) :: m_state \<Rightarrow> state"}
converts each state of the resulting machine program @{term "to_m_prog P"} into an equivalent state
of @{text P}, while @{term "to_m_state (vars P) :: state \<Rightarrow> m_state"} performs conversions the other
way around.

\null
\<close>

fun to_state :: "vname list \<Rightarrow> m_state \<Rightarrow> state" where
"to_state xs ms x = ms (addr_of xs x)"

fun to_m_state :: "vname list \<Rightarrow> state \<Rightarrow> m_state" where
"to_m_state xs s a = (if 0 < a \<and> a \<le> size xs then s (xs !! (size xs - a)) else 0)"

text \<open>
\null

Likewise, functions @{text add_stack} and @{text add_m_stack} are defined to convert machine stacks
into assembly ones and vice versa. Function @{text add_stack} takes a stack pointer and a machine
state @{text ms} as inputs, and returns a list-encoded stack mirroring the machine one maintained by
@{text ms}. Conversely, function @{text add_m_stack} takes a stack pointer, a list-encoded stack
@{text stk}, and a machine state @{text ms} as inputs, and returns the machine state obtained by
extending @{text ms} with a machine stack mirroring @{text stk}.

\null
\<close>

primrec add_stack :: "nat \<Rightarrow> m_state \<Rightarrow> stack" where
"add_stack 0 _ = []" |
"add_stack (Suc n) ms = ms (-Suc n) # add_stack n ms"

primrec add_m_stack :: "nat \<Rightarrow> stack \<Rightarrow> m_state \<Rightarrow> m_state" where
"add_m_stack 0 _ ms = ms" |
"add_m_stack (Suc n) stk ms = (add_m_stack n (tl stk) ms)(-Suc n := hd stk)"

text \<open>
\null

Here below, the semantics of machine instructions and the execution of machine programs are defined.
Such definitions resemble their assembly counterparts, but no inductive predicate like
@{const [source] iexec_pred} is needed here. In fact, @{const [source] iexec_pred} is employed to
enable Isabelle's classical reasoner to use the resulting introduction and elimination rules in the
compiler correctness proof contained in the @{text Compiler2} theory, which in the current context
shows that source code simulates assembly code. As all that is required here is to establish the
further, missing link between assembly code and machine code, the compiler correctness proof can
keep referring to assembly code -- indeed, it does not demand any change at all. Consequently, no
machine counterpart of inductive predicate @{const [source] iexec_pred} is needed in the definition
of machine instruction semantics.

As usual, any two machine configurations @{text mcf} and @{text mcf'} may be linked by a single-step
execution of a machine program @{text MP} only if @{text mcf}'s program counter points to some
instruction @{text mins} within @{text MP}. However, @{text mcf'} is not required to match, but just
to be \emph{equivalent} to the machine configuration produced by the execution of @{text mins} in
@{text mcf}; namely, program counters and stack pointers have to be equal, but machine states just
have to match up to the machine stack's top. Moreover, @{text mcf}'s machine stack has to be large
enough to store the operands, if any, required for executing @{text mins}. As shown in what follows,
these conditions are necessary for the lemmas establishing single-step assembly code-machine code
equivalence to hold.

\null
\<close>

primrec m_msp :: "m_instr \<Rightarrow> nat" where
"m_msp (M_LOADI n) = 0" |
"m_msp (M_LOAD a) = 0" |
"m_msp M_ADD = 2" |
"m_msp (M_STORE a) = 1" |
"m_msp (M_JMP n) = 0" |
"m_msp (M_JMPLESS n) = 2" |
"m_msp (M_JMPGE n) = 2"

definition msp :: "instr list \<Rightarrow> int \<Rightarrow> nat" where
"msp P i \<equiv> m_msp (to_m_instr [] (P !! i))"


fun m_iexec :: "m_instr \<Rightarrow> m_config \<Rightarrow> m_config" where
"m_iexec mins (i, ms, sp) = (case mins of
  M_LOADI n \<Rightarrow> (i + 1, ms(-1 - sp := n), sp + 1) |
  M_LOAD a \<Rightarrow> (i + 1, ms(-1 - sp := ms a), sp + 1) |
  M_ADD \<Rightarrow> (i + 1, ms(1 - sp := ms (1 - sp) + ms (-sp)), sp - 1) |
  M_STORE a \<Rightarrow> (i + 1, ms(a := ms (-sp)), sp - 1) |
  M_JMP n \<Rightarrow> (i + 1 + n, ms, sp) |
  M_JMPLESS n \<Rightarrow>
    (if ms (1 - sp) < ms (-sp) then i + 1 + n else i + 1, ms, sp - 2) |
  M_JMPGE n \<Rightarrow>
    (if ms (1 - sp) \<ge> ms (-sp) then i + 1 + n else i + 1, ms, sp - 2))"

fun m_config_equiv :: "m_config \<Rightarrow> m_config \<Rightarrow> bool" (infix "\<cong>" 55) where
"(i, ms, sp) \<cong> (i', ms', sp') =
  (i = i' \<and> sp = sp' \<and> (\<forall>a \<ge> -sp. ms a = ms' a))"

definition m_exec1 :: "m_instr list \<Rightarrow> m_config \<Rightarrow> m_config \<Rightarrow> bool"
  ("(_/ \<^bold>\<turnstile>/ _/ \<^bold>\<rightarrow>/ _)" [59, 0, 59] 60) where
"MP \<^bold>\<turnstile> mcf \<^bold>\<rightarrow> mcf' \<equiv>
  mcf' \<cong> m_iexec (MP !! fst mcf) mcf \<and> 0 \<le> fst mcf \<and> fst mcf < size MP \<and>
    m_msp (MP !! fst mcf) \<le> snd (snd mcf)"

abbreviation m_exec :: "m_instr list \<Rightarrow> m_config \<Rightarrow> m_config \<Rightarrow> bool"
  ("(_/ \<^bold>\<turnstile>/ _/ \<^bold>\<rightarrow>\<^bold>*/ _)" [59, 0, 59] 60) where
"m_exec MP \<equiv> star (m_exec1 MP)"

text \<open>
\null

Here below is the proof of lemma @{text exec1_m_exec1}, which states that, under proper assumptions,
single-step assembly code executions are simulated by machine code ones. The assumptions are that
the initial stack pointer is not less than the number of the operands taken by the instruction to be
run, and not greater than the size of the initial assembly stack. Unfortunately, the resulting stack
pointer is not guaranteed to keep fulfilling the former assumption for the next instruction; indeed,
an arbitrary instruction list is generally not so well-behaved. So, in order to prove that assembly
programs are simulated by machine ones, it needs to be proven that any machine program produced by
compiling a source one is actually well-behaved in this respect; namely, that a starting machine
configuration with stack pointer zero, as well as any intermediate configuration reached thereafter,
meet the aforesaid assumptions when executing every such program. This issue will be addressed in
the @{text Compiler2} theory.

At first glance, the need for the assumption causing this issue might appear to result from the
lower bound on the initial machine stack size introduced in @{const [source] m_exec1}'s definition.
If that were really the case, the aforesaid issue could be solved by merely dropping this condition
(leaving aside its necessity for the twin lemma @{text m_exec1_exec1} to hold, discussed later on).
Nonetheless, a more in-depth investigation shows that the incriminated assumption would be required
all the same: were it dropped, a counterexample for lemma @{text exec1_m_exec1} would arise for
@{prop "P !! pc = ADD"}, $sp = 1$ (addition rather pops \emph{two} operands from the machine stack),
and @{term "hd stk"} $\neq 0$. In fact, the initial configuration in @{text exec1_m_exec1}'s
conclusion would map addresses 0 and -1 to values 0 and @{term "hd stk"}. Hence, the configuration
correspondingly output by function @{term "m_iexec M_ADD"} would map address 0 to @{term "hd stk"},
whereas the final configuration in @{text exec1_m_exec1}'s conclusion would map it to 0. Being
$sp' = 0$, this state of affairs would not satisfy @{const [source] m_exec1}'s definition, which
would rather require the machine states of those configurations to match at every address from 0
upward.

Lemma @{text exec1_m_exec1} would fail to hold if @{text \<cong>} were replaced with @{text "="} within
@{const [source] m_exec1}'s definition. In fact, function @{const to_m_state} invariably returns
machine states mapping any nonpositive address to zero, and function @{const add_m_stack} leaves
unchanged any value below the machine stack's top. Thus, upon any machine instruction @{text mins}
that pops a value $i \neq 0$ from the stack's top address @{text a}, the configuration obtained
by applying function @{term "m_iexec mins"} to the initial configuration in @{text exec1_m_exec1}'s
conclusion maps @{text a} to @{text i}, whereas the final configuration maps @{text a} to 0. As a
result, the machine states of those configurations match only up to the machine stack's top, exactly
as required using @{text \<cong>} in @{const [source] m_exec1}'s definition.

\null
\<close>

lemma inth_map [simp]:
 "\<lbrakk>0 \<le> i; i < size xs\<rbrakk> \<Longrightarrow> (map f xs) !! i = f (xs !! i)"
by (induction xs arbitrary: i, simp_all)

lemma inth_set [simp]:
 "\<lbrakk>0 \<le> i; i < size xs\<rbrakk> \<Longrightarrow> xs !! i \<in> set xs"
by (induction xs arbitrary: i, simp_all)

lemma vars_dist:
 "distinct (vars P)"
by (induction P, simp_all split: instr.split)

lemma vars_load:
 "\<lbrakk>0 \<le> i; i < size P; P !! i = LOAD x\<rbrakk> \<Longrightarrow> x \<in> set (vars P)"
by (induction P arbitrary: i, simp, fastforce split: if_split_asm)

lemma vars_store:
 "\<lbrakk>0 \<le> i; i < size P; P !! i = STORE x\<rbrakk> \<Longrightarrow> x \<in> set (vars P)"
by (induction P arbitrary: i, simp, fastforce split: if_split_asm)

lemma addr_of_max:
 "addr_of xs x \<le> size xs"
by (induction xs, simp_all)

lemma addr_of_neq:
 "1 + size xs \<noteq> addr_of xs x"
by (insert addr_of_max [of xs x], simp)

lemma addr_of_correct:
 "x \<in> set xs \<Longrightarrow> xs !! (size xs - addr_of xs x) = x"
by (induction xs, simp, clarsimp, erule contrapos_pp, rule addr_of_neq)

lemma addr_of_nneg:
 "0 \<le> addr_of xs x"
by (induction xs, simp_all)

lemma addr_of_set:
 "x \<in> set xs \<Longrightarrow> 0 < addr_of xs x"
by (induction xs, auto)

lemma addr_of_unique:
 "\<lbrakk>distinct xs; 0 < a; a \<le> size xs\<rbrakk> \<Longrightarrow> addr_of xs (xs !! (size xs - a)) = a"
by (induction xs, auto)

lemma add_m_stack_nneg:
 "0 \<le> a \<Longrightarrow> add_m_stack n stk ms a = ms a"
by (induction n arbitrary: stk, simp_all)

lemma add_m_stack_hd:
 "0 < n \<Longrightarrow> add_m_stack n stk ms (-n) = hd stk"
by (cases n, simp_all)

lemma add_m_stack_hd2:
 "1 < n \<Longrightarrow> add_m_stack n stk ms (1 - int n) = hd2 stk"
by (cases n, simp_all add: add_m_stack_hd)

lemma add_m_stack_nth:
 "\<lbrakk>-n \<le> a; n \<le> length stk\<rbrakk> \<Longrightarrow>
    add_m_stack n stk ms a = (if 0 \<le> a then ms a else stk ! (nat (n + a)))"
by (induction n arbitrary: stk, auto intro: hd_conv_nth simp: add_m_stack_nneg
 nth_tl Suc_nat_eq_nat_zadd1 ac_simps)

lemma exec1_m_exec1 [simplified Let_def]:
 "\<lbrakk>P \<turnstile> (pc, s, stk) \<rightarrow> (pc', s', stk'); msp P pc \<le> sp; sp \<le> length stk\<rbrakk> \<Longrightarrow>
    let sp' = sp + length stk' - length stk in to_m_prog P \<^bold>\<turnstile>
      (pc, add_m_stack sp stk (to_m_state (vars P) s), sp) \<^bold>\<rightarrow>
      (pc', add_m_stack sp' stk' (to_m_state (vars P) s'), sp')"
proof (auto dest: vars_load vars_store addr_of_set intro: addr_of_max
 simp: msp_def exec1_def m_exec1_def vars_load addr_of_correct addr_of_nneg
 add_m_stack_nneg add_m_stack_hd add_m_stack_hd2 split: instr.split)
qed (auto dest: vars_store simp: add_m_stack_nth nth_tl Suc_nat_eq_nat_zadd1
 of_nat_diff vars_dist addr_of_correct addr_of_unique)

text \<open>
\null

Here below is the proof of lemma @{text m_exec1_exec1}, which reverses the previous one and states
that single-step machine code executions are simulated by assembly code ones. As opposed to lemma
@{thm [source] exec1_m_exec1}, the present one does not require any assumption apart from having
two arbitrary machine configurations linked by a single-step program execution. Hence, this time
there is no obstacle to proving lemma @{text m_exec_exec}, which generalizes @{text m_exec1_exec1}
to multiple-step program executions, as a direct consequence of @{text m_exec1_exec1} via induction
over the reflexive transitive closure of binary predicate @{term "m_exec1 (to_m_prog P)"}, where
@{text P} is the given, arbitrary assembly program.

If the condition that the initial machine stack be large enough to store the operands of the current
instruction were removed from @{const [source] m_exec1}'s definition, lemma @{text m_exec1_exec1}
would not hold. A counterexample would be the case where @{prop "P !! pc = ADD"}, $sp = 1$, and
@{prop "stk = []"}. Being $sp' = 0$, the final assembly stack in @{text m_exec1_exec1}'s conclusion
would be empty, whereas according to @{const [source] exec1}'s definition, the assembly stack
resulting from the execution of an addition cannot be empty.

\null
\<close>

lemma addr_of_nset:
 "x \<notin> set xs \<Longrightarrow> addr_of xs x = 0"
by (induction xs, auto split: if_split_asm)

lemma addr_of_inj:
 "inj_on (addr_of xs) (set xs)"
by (subst inj_on_def, clarify, induction xs, simp_all split: if_split_asm,
 drule sym, (subst (asm) add.commute, erule contrapos_pp, rule addr_of_neq)+)

lemma addr_of_neq2:
 "\<lbrakk>x \<in> set xs; x' \<noteq> x\<rbrakk> \<Longrightarrow> addr_of xs x' \<noteq> addr_of xs x"
by (cases "x' \<in> set xs", erule contrapos_nn, rule inj_onD [OF addr_of_inj],
 simp_all, drule addr_of_set, drule addr_of_nset, simp)

lemma to_state_eq:
 "\<forall>a \<ge> 0. ms' a = ms a \<Longrightarrow> to_state xs ms' = to_state xs ms"
by (rule ext, simp, induction xs, simp_all)

lemma to_state_upd:
 "\<lbrakk>\<forall>a \<ge> 0. ms' a = (if a = addr_of xs x then i else ms a); x \<in> set xs\<rbrakk> \<Longrightarrow>
    to_state xs ms' = (to_state xs ms)(x := i)"
by (rule ext, simp, rule conjI, rule_tac [!] impI, simp add: addr_of_nneg,
 drule addr_of_neq2, simp, simp add: addr_of_nneg)

lemma add_stack_eq:
 "\<lbrakk>\<forall>a \<in> {-m..<0}. ms' a = ms a; m = n\<rbrakk> \<Longrightarrow> add_stack m ms' = add_stack n ms"
by (induction m arbitrary: n, auto)

lemma add_stack_eq2:
 "\<lbrakk>\<forall>a \<in> {-n..<0}. ms' a = (if a = -n then i else ms a); 0 < n\<rbrakk> \<Longrightarrow>
    add_stack n ms' = i # add_stack (n - 1) ms"
by (cases n, simp_all add: add_stack_eq)

lemma add_stack_hd:
 "0 < n \<Longrightarrow> hd (add_stack n ms) = ms (-n)"
by (cases n, simp_all)

lemma add_stack_hd2:
 "1 < n \<Longrightarrow> hd2 (add_stack n ms) = ms (1 - int n)"
by (induction n, simp_all add: add_stack_hd)

lemma add_stack_nnil:
 "0 < n \<Longrightarrow> add_stack n ms \<noteq> []"
by (cases n, simp_all)

lemma add_stack_nnil2:
 "1 < n \<Longrightarrow> tl (add_stack n ms) \<noteq> []"
by (induction n, simp_all add: add_stack_nnil)

lemma add_stack_tl:
 "tl (add_stack n ms) = add_stack (n - 1) ms"
by (cases n, simp_all)

lemma m_exec1_exec1 [simplified]:
 "to_m_prog P \<^bold>\<turnstile> (pc, ms, sp) \<^bold>\<rightarrow> (pc', ms', sp') \<Longrightarrow>
    P \<turnstile> (pc, to_state (vars P) ms, add_stack sp ms @ stk) \<rightarrow>
      (pc', to_state (vars P) ms', add_stack sp' ms' @ stk)"
proof (auto elim!: vars_store intro!: to_state_eq to_state_upd add_stack_eq
 simp: exec1_def m_exec1_def iexec_simp add_stack_hd add_stack_hd2
 add_stack_nnil add_stack_nnil2 split: instr.split_asm)
qed (subst add_stack_eq2, fastforce+, simp_all add: add_stack_tl, rule arg_cong,
 auto dest!: vars_store addr_of_set intro: add_stack_eq)

lemma m_exec_exec:
 "to_m_prog P \<^bold>\<turnstile> (pc, ms, sp) \<^bold>\<rightarrow>\<^bold>* (pc', ms', sp') \<Longrightarrow>
    P \<turnstile> (pc, to_state (vars P) ms, add_stack sp ms @ stk) \<rightarrow>*
      (pc', to_state (vars P) ms', add_stack sp' ms' @ stk)"
by (induction _ "(pc, ms, sp)" "(pc', ms', sp')" arbitrary: pc ms sp rule:
 star.induct, simp_all add: split_paired_all, drule m_exec1_exec1,
 auto intro: star_trans)


subsection "Verification infrastructure"

lemma iexec_shift [simp]: 
 "((n + i', s', stk') = iexec ins (n + i, s, stk)) =
    ((i', s', stk') = iexec ins (i, s, stk))"
by (auto split: instr.split)

lemma exec1_appendR:
 "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow> c'"
by (auto simp: exec1_def)

lemma exec_appendR:
 "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow>* c'"
by (induction rule: star.induct) (fastforce intro: star.step exec1_appendR)+

lemma exec1_appendL:
  fixes i i' :: int 
  shows "P \<turnstile> (i, s, stk) \<rightarrow> (i', s', stk') \<Longrightarrow>
    P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow> (size P' + i', s', stk')"
by (auto simp: exec1_def iexec_simp simp del: iexec.simps)

lemma exec_appendL:
  fixes i i' :: int 
  shows "P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk') \<Longrightarrow>
    P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow>* (size P' + i', s', stk')"
by (induction rule: exec_induct) (blast intro: star.step exec1_appendL)+

lemma exec_Cons_1 [intro]:
 "P \<turnstile> (0, s, stk) \<rightarrow>* (j, t, stk') \<Longrightarrow>
    ins # P \<turnstile> (1, s, stk) \<rightarrow>* (1 + j, t, stk')"
by (drule exec_appendL [where P' = "[ins]"]) simp

lemma exec_appendL_if [intro]:
  fixes i i' j :: int
  shows "\<lbrakk>size P' \<le> i; P \<turnstile> (i - size P', s, stk) \<rightarrow>* (j, s', stk');
    i' = size P' + j\<rbrakk> \<Longrightarrow>
      P' @ P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk')"
by (drule exec_appendL [where P' = P']) simp

lemma exec_append_trans [intro]:
  fixes i' i'' j'' :: int
  shows "\<lbrakk>P \<turnstile> (0, s, stk) \<rightarrow>* (i', s', stk'); size P \<le> i';
    P' \<turnstile> (i' - size P, s', stk') \<rightarrow>* (i'', s'', stk''); j'' = size P + i''\<rbrakk> \<Longrightarrow>
      P @ P' \<turnstile> (0, s, stk) \<rightarrow>* (j'', s'', stk'')"
by (metis star_trans [OF exec_appendR exec_appendL_if])

declare Let_def [simp]


subsection "Compilation"

text \<open>
As mentioned previously, the definitions of the functions modeling source-to-assembly compilation,
reported here below, need not be changed. Particularly, function @{text ccomp} can be used to define
some abbreviations for functions @{const to_m_prog}, @{const to_state}, and @{const to_m_state}, in
which their first parameter (an assembly program for @{const to_m_prog}, a list of variables for the
other two functions) is replaced with a command. In fact, the compiler completeness and correctness
properties apply to machine programs resulting from the compilation of source programs, that is, of
commands. Consequently, such abbreviations, defined here below as well, can be used to express those
properties in a more concise form.

\null
\<close>

primrec acomp :: "aexp \<Rightarrow> instr list" where
"acomp (N i) = [LOADI i]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a\<^sub>1 a\<^sub>2) = acomp a\<^sub>1 @ acomp a\<^sub>2 @ [ADD]"

fun bcomp :: "bexp \<times> bool \<times> int \<Rightarrow> instr list" where
"bcomp (Bc v, f, i) = (if v = f then [JMP i] else [])" |
"bcomp (Not b, f, i) = bcomp (b, \<not> f, i)" |
"bcomp (And b\<^sub>1 b\<^sub>2, f, i) =
  (let cb\<^sub>2 = bcomp (b\<^sub>2, f, i);
     cb\<^sub>1 = bcomp (b\<^sub>1, False, size cb\<^sub>2 + (if f then 0 else i))
   in cb\<^sub>1 @ cb\<^sub>2)" |
"bcomp (Less a\<^sub>1 a\<^sub>2, f, i) =
  acomp a\<^sub>1 @ acomp a\<^sub>2 @ (if f then [JMPLESS i] else [JMPGE i])"

primrec ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^sub>1;; c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp c\<^sub>1; cc\<^sub>2 = ccomp c\<^sub>2; cb = bcomp (b, False, size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp (WHILE b DO c) =
  (let cc = ccomp c; cb = bcomp (b, False, size cc + 1)
   in cb @ cc @ [JMP (- (size cb + size cc + 1))])"


abbreviation m_ccomp :: "com \<Rightarrow> m_instr list" where
"m_ccomp c \<equiv> to_m_prog (ccomp c)"

abbreviation m_state :: "com \<Rightarrow> state \<Rightarrow> m_state" where
"m_state c \<equiv> to_m_state (vars (ccomp c))"

abbreviation state :: "com \<Rightarrow> m_state \<Rightarrow> state" where
"state c \<equiv> to_state (vars (ccomp c))"


lemma acomp_correct [intro]:
 "acomp a \<turnstile> (0, s, stk) \<rightarrow>* (size (acomp a), s, aval a s # stk)"
by (induction a arbitrary: stk) fastforce+

lemma bcomp_correct [intro]:
  fixes i :: int
  shows "0 \<le> i \<Longrightarrow> bcomp (b, f, i) \<turnstile> (0, s, stk) \<rightarrow>*
    (size (bcomp (b, f, i)) + (if f = bval b s then i else 0), s, stk)"
proof (induction b arbitrary: f i)
  case Not
  from Not(1) [where f = "\<not> f"] Not(2)
  show ?case
    by fastforce
next
  case (And b\<^sub>1 b\<^sub>2)
  from And(1) [of "if f then size (bcomp (b\<^sub>2, f, i)) else
    size (bcomp (b\<^sub>2, f, i)) + i" False] And(2) [of i f] And(3)
  show ?case
    by fastforce
qed fastforce+


subsection "Preservation of semantics"

text \<open>
Like \<^cite>\<open>"Nipkow21-2"\<close>, this theory ends with the proof of theorem @{text ccomp_bigstep}, which
states that source programs are simulated by assembly ones, as proving that assembly programs are in
turn simulated by machine ones is still a pending task. This missing link will be established in the
@{text Compiler2} theory. Such a state of affairs might appear as nothing but an extravagant choice:
if the original development detailed in \<^cite>\<open>"Nipkow21-1"\<close> addresses the ``easy'' direction of the
program bisimulation proof in the @{text Compiler} theory, why moving its machine code add-on to the
@{text Compiler2} theory? The bad news here are that the move has occurred as proving that assembly
programs are simulated by machine ones is no longer ``easy''. Indeed, this task demands the further
reasoning tools used in the @{text Compiler2} theory to cope with the reverse, ``hard'' direction of
the program bisimulation proof. On the other hand, the good news are that such tools, in the form
introduced in \<^cite>\<open>"Noce21"\<close>, are sufficiently general and powerful to also accomplish that task,
as will be shown shortly.

\null
\<close>

theorem ccomp_bigstep:
 "(c, s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0, s, stk) \<rightarrow>* (size (ccomp c), t, stk)"
proof (induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case
    by (fastforce simp: fun_upd_def cong: if_cong)
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  let ?cc\<^sub>1 = "ccomp c\<^sub>1"
  let ?cc\<^sub>2 = "ccomp c\<^sub>2"
  have "?cc\<^sub>1 @ ?cc\<^sub>2 \<turnstile> (0, s\<^sub>1, stk) \<rightarrow>* (size ?cc\<^sub>1, s\<^sub>2, stk)"
    using Seq.IH(1) by fastforce
  moreover have "?cc\<^sub>1 @ ?cc\<^sub>2 \<turnstile> (size ?cc\<^sub>1, s\<^sub>2, stk) \<rightarrow>*
    (size (?cc\<^sub>1 @ ?cc\<^sub>2), s\<^sub>3, stk)"
    using Seq.IH(2) by fastforce
  ultimately show ?case
    by simp (blast intro: star_trans)
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp (b, False, size ?cc + 1)"
  let ?cw = "ccomp (WHILE b DO c)"
  have "?cw \<turnstile> (0, s\<^sub>1, stk) \<rightarrow>* (size ?cb, s\<^sub>1, stk)"
    using \<open>bval b s\<^sub>1\<close> by fastforce
  moreover have "?cw \<turnstile> (size ?cb, s\<^sub>1, stk) \<rightarrow>* (size ?cb + size ?cc, s\<^sub>2, stk)"
    using WhileTrue.IH(1) by fastforce
  moreover have "?cw \<turnstile> (size ?cb + size ?cc, s\<^sub>2, stk) \<rightarrow>* (0, s\<^sub>2, stk)"
    by fastforce
  moreover have "?cw \<turnstile> (0, s\<^sub>2, stk) \<rightarrow>* (size ?cw, s\<^sub>3, stk)"
    by (rule WhileTrue.IH(2))
  ultimately show ?case
    by (blast intro: star_trans)
qed fastforce+


declare Let_def [simp del]

lemma impCE2 [elim!]:
 "\<lbrakk>P \<longrightarrow> Q; \<not> P \<Longrightarrow> R; P \<Longrightarrow> Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by blast

lemma Suc_lessI2 [intro!]:
 "\<lbrakk>m < n; m \<noteq> n - 1\<rbrakk> \<Longrightarrow> Suc m < n"
by simp

end
