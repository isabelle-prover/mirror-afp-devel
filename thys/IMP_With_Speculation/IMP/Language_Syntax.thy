section "A Simple Imperative Language"

theory Language_Syntax imports Language_Prelims "Relative_Security.Trivia"  begin

text \<open>A Simple Imperative Language with arrays, inputs and outputs, and speculation fences, based off the syntax for IMP in Concrete Semantics \cite{Concrete}\<close>


text \<open>Scalar variables are defined as strings, and so are the array variables\<close>
type_synonym vname = string
type_synonym avname = string

text \<open>Since the Spectre benchmark examples reason about integer variables, we define our set of values to be integers\<close>
type_synonym val = int


text \<open>We define our set of locations to be integers\<close>
type_synonym loc = nat

subsection "Arithmetic and Boolean Expressions"


text \<open>Arithmetic expressions can either be literals, variables or array variables (array variable name, index), or some operation on these. The arithmetic operators we capture in an expression are addition and multiplication. 
For boolean expressions we capture negation and conjunction, and the arithmetic comparison operator "less than" where equality of two arithmetic terms is later defined in terms of these constructors\<close>

datatype aexp = N int | V vname | VA avname aexp | Plus aexp aexp | Times aexp aexp |
    Ite bexp aexp aexp | Fun aexp aexp
and bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp 

text \<open>To enable reasoning about more subtle Spectre-like examples require the existence of trusted and untrusted I/O channels\<close>
datatype trustStat = Trusted ("T")| Untrusted ("U")

consts func :: "aexp \<times> aexp \<Rightarrow> val"

text \<open>A little syntax magic to write larger states compactly:\<close>

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"


subsection "Commmands"

text \<open>The language defined by this grammar capture standard basic mechanisms for manipulating scalar and array variables, and (un)conditional jumps, using Jump and IfJump, as control structures. 
It is also an I/O interactive language, accepting inputs on various input channels and producing outputs on various output channels.
Most of the commands are standard, however there is an inclusion of Fences and Masking commands which are non-standard.
The "Fence" command models the lfence instruction which prevents further speculative execution and is crucial in capturing key Spectre benchmark examples.
The Mask command models Speculative Load Hardening (SLH), which masks variable values with respect to a given condition, contextually it can protect against leaks by masking values during misspeculation.
It can be read as "M var I b T exp1 E exp2 == IF b THEN var = exp1 ELSE var = exp2"\<close>

datatype (discs_sels) com = 
        Start
      | Skip 
      
      | getInput trustStat vname ("(Input _/ _)"  [0, 61] 61)
      | Output trustStat aexp ("(Output _/ _)"  [0, 61] 61)
      | Fence
      | Jump nat 
      | Assign vname aexp ("_ ::= _" [1000, 61] 61)
      | ArrAssign avname aexp aexp ("_ [_] ::= _" [1000, 61] 61)
      | IfJump bexp nat nat ("(IfJump _/ _/ _)"  [0, 0, 61] 61)
  (* this indicates two program counters: where to jump if condition is true, 
   and where if condition is false *)

text \<open>A predicate which determines whether or not a memory read occurs in an arithmetic expression\<close>
fun isReadMemory ::"aexp \<Rightarrow> bool" where
"isReadMemory (N n) = False" |
"isReadMemory (V x) = False" |
"isReadMemory (VA a i) = True" |
"isReadMemory (Plus a1 a2) = (isReadMemory a1 \<or> isReadMemory a2)"|
"isReadMemory (Times a1 a2) = (isReadMemory a1 \<or> isReadMemory a2)"

subsection "Stores, States and Configurations"

text \<open>Defining a variable store, array variable store and a heap. 
The variable store is as standard, mapping variable names to values.
The array variable store maps array name, to a base address in the and the size of the array.
The heap maps memory locations to values\<close>
datatype vstore = Vstore (vstore:"vname \<Rightarrow> val") 
datatype avstore = Avstore (avstore:"avname \<Rightarrow> loc * nat") 
datatype heap = Heap (hheap:"loc \<Rightarrow> val") 

text \<open>A given value of an element in an array is assigned in the heap at location "array base+index". 
For example if the array "a1" has array base = 0, then the value a1[3] can be found at memory location 3 in the heap\<close>
definition array_base :: "avname \<Rightarrow> avstore \<Rightarrow> loc" where
"array_base arr avst \<equiv> case avst of (Avstore as) \<Rightarrow> fst (as arr)"

definition array_bound :: "avname \<Rightarrow> avstore \<Rightarrow> nat" where
"array_bound arr avst \<equiv> case avst of (Avstore as) \<Rightarrow> snd (as arr)"

definition array_loc :: "avname \<Rightarrow> nat \<Rightarrow> avstore \<Rightarrow> loc" where
"array_loc arr i avst \<equiv> array_base arr avst + i"

lemma array_locBase: "array_base arr avst = array_loc arr 0 avst"
  by (simp add: array_loc_def)

text \<open>A state consists of: (command, variable store, heap, next free location in the heap). \<close>
datatype state = State (getVstore: vstore) (getAvstore: avstore) (getHeap: heap) (getFree: nat) 


fun getHheap where "getHheap (State vst avst h p) = hheap h" 

text \<open>A configuration for the normal semantics consists of: (command,state,the set of read memory locations so far).\<close>

type_synonym pcounter = nat 

datatype config = Config (pcOf: pcounter) (stateOf: state) 

(*standard getters to help simplify notation*)
fun vstoreOf where "vstoreOf (Config pc s) = vstore (getVstore s)"
fun avstoreOf where "avstoreOf (Config pc s) = avstore (getAvstore s)"
fun heapOf where "heapOf (Config pc s) = getHeap s"
fun freeOf where "freeOf (Config pc s) = getFree s"
fun hheapOf where "hheapOf (Config pc s) = getHheap s"


subsection "Evaluation of arithmetic and boolean expressions"

text \<open>A standard recursive function which evaluates a given expression\<close>
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" 
and bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"aval (N n) s = n" 
|
"aval (V x) s = vstore (getVstore s) x" 
|
"aval (VA a i) s = getHheap s (array_loc a (nat(aval i s)) (getAvstore s))" 
|
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"
|
"aval (Times a1 a2) s = aval a1 s * aval a2 s"
|
"aval (Ite b a1 a2) s = (if bval b s then aval a1 s else aval a2 s)"
|
"aval (Fun x y) s = func (x, y)"
|
"bval (Bc v) s = v" 
|
"bval (Not b) s = (\<not> bval b s)" 
|
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" 
|
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"


text \<open>An arithmetic equivalence of two terms as a boolean expression\<close>
definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a1 a2 \<equiv> And (Not (Less a1 a2)) (Not (Less a2 a1))"

lemma Eq_verif:"bval (Eq a1 a2) s \<longleftrightarrow> aval a1 s = aval a2 s"
  apply standard
  unfolding Eq_def by simp+


fun outOf :: "com \<Rightarrow> state \<Rightarrow> val" where 
"outOf c s = (case c of Output T aexp \<Rightarrow> aval aexp s |_ \<Rightarrow> undefined)"



end