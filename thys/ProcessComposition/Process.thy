theory Process
  imports Resource
begin

section\<open>Process Compositions\<close>

text\<open>
  We define process compositions to describe how larger processes are built from smaller ones from
  the perspective of how outputs of some actions serve as inputs for later actions.
  Our process compositions form a tree, with actions as leaves and composition operations as
  internal nodes.
  We use resources to represent the inputs and outputs of processes.
\<close>

subsection\<open>Datatype, Input, Output and Validity\<close>

text\<open>
  Process composition datatype with primitive actions, composition operations and resource actions.
  We use the following type variables:
  \<^item> @{typ 'a} for linear resource atoms,
  \<^item> @{typ 'b} for copyable resource atoms,
  \<^item> @{typ 'l} for primitive action labels, and
  \<^item> @{typ 'm} for primitive action metadata.
\<close>
datatype ('a, 'b, 'l, 'm) process =
    Primitive "('a, 'b) resource" "('a, 'b) resource" 'l 'm
    \<comment> \<open>Primitive action with given input, ouptut, label and metadata\<close>
  | Seq "('a, 'b, 'l, 'm) process" "('a, 'b, 'l, 'm) process"
    \<comment> \<open>Sequential composition\<close>
  | Par "('a, 'b, 'l, 'm) process" "('a, 'b, 'l, 'm) process"
    \<comment> \<open>Parallel composition\<close>
  | Opt "('a, 'b, 'l, 'm) process" "('a, 'b, 'l, 'm) process"
    \<comment> \<open>Optional composition\<close>
  | Represent "('a, 'b, 'l, 'm) process"
    \<comment> \<open>Representation of a process composition as a repeatably exectuable resource\<close>
  | Identity "('a, 'b) resource"
    \<comment> \<open>Identity action\<close>
  | Swap "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Swap action\<close>
  | InjectL "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Left injection\<close>
  | InjectR "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Right injection\<close>
  | OptDistrIn "('a, 'b) resource" "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Distribution into branches of a non-deterministic resource\<close>
  | OptDistrOut "('a, 'b) resource" "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Distribution out of branches of a non-deterministic resource\<close>
  | Duplicate "'b"
    \<comment> \<open>Duplication of a copyable resource\<close>
  | Erase "'b"
    \<comment> \<open>Discarding a copyable resource\<close>
  | Apply "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Applying an executable resource\<close>
  | Repeat "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Duplicating a repeatably executable resource\<close>
  | Close "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Discarding a repeatably executable resource\<close>
  | Once "('a, 'b) resource" "('a, 'b) resource"
    \<comment> \<open>Converting a repeatably executable resource into a plain execuable resource\<close>
  | Forget "('a, 'b) resource"
    \<comment> \<open>Forgetting all details about a resource\<close>

text\<open>
  Each process composition has a well defined input and output resource, derived recursively from
  the individual actions that constitute it.
\<close>
primrec input :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b) resource"
  where
    "input (Primitive ins outs l m) = ins"
  | "input (Seq p q) = input p"
  | "input (Par p q) = input p \<odot> input q"
  | "input (Opt p q) = NonD (input p) (input q)"
  | "input (Represent p) = Empty"
  | "input (Identity a) = a"
  | "input (Swap a b) = a \<odot> b"
  | "input (InjectL a b) = a"
  | "input (InjectR a b) = b"
  | "input (OptDistrIn a b c) = a \<odot> (NonD b c)"
  | "input (OptDistrOut a b c) = NonD (a \<odot> b) (a \<odot> c)"
  | "input (Duplicate a) = Copyable a"
  | "input (Erase a) = Copyable a"
  | "input (Apply a b) = a \<odot> (Executable a b)"
  | "input (Repeat a b) = Repeatable a b"
  | "input (Close a b) = Repeatable a b"
  | "input (Once a b) = Repeatable a b"
  | "input (Forget a) = a"

text\<open>Input of mapped process is accordingly mapped input\<close>
lemma map_process_input [simp]:
  "input (map_process f g h i x) = map_resource f g (input x)"
  by (induct x) simp_all

primrec "output" :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b) resource"
  where
    "output (Primitive ins outs l m) = outs"
  | "output (Seq p q) = output q"
  | "output (Par p q) = output p \<odot> output q"
  | "output (Opt p q) = output p"
  | "output (Represent p) = Repeatable (input p) (output p)"
  | "output (Identity a) = a"
  | "output (Swap a b) = b \<odot> a"
  | "output (InjectL a b) = NonD a b"
  | "output (InjectR a b) = NonD a b"
  | "output (OptDistrIn a b c) = NonD (a \<odot> b) (a \<odot> c)"
  | "output (OptDistrOut a b c) = a \<odot> (NonD b c)"
  | "output (Duplicate a) = Copyable a \<odot> Copyable a"
  | "output (Erase a) = Empty"
  | "output (Apply a b) = b"
  | "output (Repeat a b) = (Repeatable a b) \<odot> (Repeatable a b)"
  | "output (Close a b) = Empty"
  | "output (Once a b) = Executable a b"
  | "output (Forget a) = Anything"

text\<open>Output of mapped process is accordingly mapped output\<close>
lemma map_process_output [simp]:
  "output (map_process f g h i x) = map_resource f g (output x)"
  by (induct x) simp_all

text\<open>
  Not all process compositions are valid.
  While we consider all individual actions to be valid, we impose two conditions on composition
  operations beyond the validity of their children:
  \<^item> Sequential composition requires that the output of the first process be the input of the second.
  \<^item> Optional composition requires that the two processes arrive at the same output.
\<close>
primrec valid :: "('a, 'b, 'l, 'm) process \<Rightarrow> bool"
  where
    "valid (Primitive ins outs l m) = True"
  | "valid (Seq p q) = (output p = input q \<and> valid p \<and> valid q)"
  | "valid (Par p q) = (valid p \<and> valid q)"
  | "valid (Opt p q) = (valid p \<and> valid q \<and> output p = output q)"
  | "valid (Represent p) = valid p"
  | "valid (Identity a) = True"
  | "valid (Swap a b) = True"
  | "valid (InjectL a b) = True"
  | "valid (InjectR a b) = True"
  | "valid (OptDistrIn a b c) = True"
  | "valid (OptDistrOut a b c) = True"
  | "valid (Duplicate a) = True"
  | "valid (Erase a) = True"
  | "valid (Apply a b) = True"
  | "valid (Repeat a b) = True"
  | "valid (Close a b) = True"
  | "valid (Once a b) = True"
  | "valid (Forget a) = True"

text\<open>Process mapping preserves validity\<close>
lemma map_process_valid [simp]:
  "valid x \<Longrightarrow> valid (map_process f g h i x)"
  by (induct x) simp_all

text\<open>
  However, it does not necessarily preserve invalidity if there exist two distinct linear or
  copyable resource atoms
\<close>
lemma
    fixes g h i and a b :: 'a
  assumes "a \<noteq> b"
  obtains f and x :: "('a, 'b, 'l, 'm) process"
    where "\<not> valid x" and "valid (map_process f g h i x)"
proof
  let ?x = "Seq (Identity (Res a)) (Identity (Res b))"
  let ?f = "\<lambda>x. undefined" \<comment> \<open>Note that the value used can be anything\<close>
  show "\<not> valid ?x"
    using assms resource_res_eq by fastforce
  show "valid (map_process ?f g h i ?x)"
    by simp
qed
lemma
    fixes f h i and a b :: 'b
  assumes "a \<noteq> b"
  obtains g and x :: "('a, 'b, 'l, 'm) process"
    where "\<not> valid x" and "valid (map_process f g h i x)"
proof
  let ?x = "Seq (Identity (Copyable a)) (Identity (Copyable b))"
  let ?g = "\<lambda>x. undefined" \<comment> \<open>Note that the value used can be anything\<close>
  show "\<not> valid ?x"
    using assms resource_copyable_eq by fastforce
  show "valid (map_process f ?g h i ?x)"
    by simp
qed

text\<open>If the resource map is injective then mapping with it does not change validity\<close>
lemma map_process_valid_eq:
  assumes "inj f" (* TODO could be weakened to "inj_on f (set1_process x)" *)
      and "inj g" (* TODO could be weakened to "inj_on g (set2_process x)" *)
    shows "valid x = valid (map_process f g h i x)"
  using assms by (induct x ; simp ; metis injD resource.inj_map)

subsection\<open>Gathering Primitive Actions\<close>

text\<open>
  As primitive actions represent assumptions about what we can do in the modelling domain, it is
  often useful to gather them.
\<close>

text\<open>
  When we want to talk about only primitive actions, we represent them with a quadruple of input,
  output, label and metadata, just as the parameters to the @{const Primitive} constructor.
\<close>
type_synonym ('a, 'b, 'l, 'm) prim_pars = "('a, 'b) resource \<times> ('a, 'b) resource \<times> 'l \<times> 'm"

text\<open>Uncurried version of @{const Primitive} to use with @{type prim_pars}\<close>
fun Primitive_unc :: "('a, 'b, 'l, 'm) prim_pars \<Rightarrow> ('a, 'b, 'l, 'm) process"
  where "Primitive_unc (a, b, l, m) = Primitive a b l m"

text\<open>Gather the primitives recursively from the composition, preserving their order\<close>
primrec primitives :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b, 'l, 'm) prim_pars list"
  where
    "primitives (Primitive ins outs l m) = [(ins, outs, l, m)]"
  | "primitives (Seq p q) = primitives p @ primitives q"
  | "primitives (Par p q) = primitives p @ primitives q"
  | "primitives (Opt p q) = primitives p @ primitives q"
  | "primitives (Represent p) = primitives p"
  | "primitives (Identity a) = []"
  | "primitives (Swap a b) = []"
  | "primitives (InjectL a b) = []"
  | "primitives (InjectR a b) = []"
  | "primitives (OptDistrIn a b c) = []"
  | "primitives (OptDistrOut a b c) = []"
  | "primitives (Duplicate a) = []"
  | "primitives (Erase a) = []"
  | "primitives (Apply a b) = []"
  | "primitives (Repeat a b) = []"
  | "primitives (Close a b) = []"
  | "primitives (Once a b) = []"
  | "primitives (Forget a) = []"

text\<open>Primitives of mapped process are accordingly mapped primitives\<close>
lemma map_process_primitives [simp]:
  " primitives (map_process f g h i x)
  = map (\<lambda>(a, b, l, m). (map_resource f g a, map_resource f g b, h l, i m)) (primitives x)"
  by (induct x) simp_all

subsection\<open>Resource Refinement in Processes\<close>

text\<open>We can apply @{const refine_resource} systematically throughout a process composition\<close>
primrec process_refineRes ::
    "('a \<Rightarrow> ('x, 'y) resource) \<Rightarrow> ('b \<Rightarrow> 'y) \<Rightarrow> ('a, 'b, 'l, 'm) process \<Rightarrow> ('x, 'y, 'l, 'm) process"
  where
    "process_refineRes f g (Primitive ins outs l m) =
      Primitive (refine_resource f g ins) (refine_resource f g outs) l m"
  | "process_refineRes f g (Identity a) = Identity (refine_resource f g a)"
  | "process_refineRes f g (Swap a b) = Swap (refine_resource f g a) (refine_resource f g b)"
  | "process_refineRes f g (Seq p q) = Seq (process_refineRes f g p) (process_refineRes f g q)"
  | "process_refineRes f g (Par p q) = Par (process_refineRes f g p) (process_refineRes f g q)"
  | "process_refineRes f g (Opt p q) = Opt (process_refineRes f g p) (process_refineRes f g q)"
  | "process_refineRes f g (InjectL a b) = InjectL (refine_resource f g a) (refine_resource f g b)"
  | "process_refineRes f g (InjectR a b) = InjectR (refine_resource f g a) (refine_resource f g b)"
  | "process_refineRes f g (OptDistrIn a b c) =
      OptDistrIn (refine_resource f g a) (refine_resource f g b) (refine_resource f g c)"
  | "process_refineRes f g (OptDistrOut a b c) =
      OptDistrOut (refine_resource f g a) (refine_resource f g b) (refine_resource f g c)"
  | "process_refineRes f g (Duplicate a) = Duplicate (g a)"
  | "process_refineRes f g (Erase a) = Erase (g a)"
  | "process_refineRes f g (Represent p) = Represent (process_refineRes f g p)"
  | "process_refineRes f g (Apply a b) = Apply (refine_resource f g a) (refine_resource f g b)"
  | "process_refineRes f g (Repeat a b) = Repeat (refine_resource f g a) (refine_resource f g b)"
  | "process_refineRes f g (Close a b) = Close (refine_resource f g a) (refine_resource f g b)"
  | "process_refineRes f g (Once a b) = Once (refine_resource f g a) (refine_resource f g b)"
  | "process_refineRes f g (Forget a) = Forget (refine_resource f g a)"

text\<open>This behaves well with the input, output and primitives, and preserves validity\<close>
lemma process_refineRes_input [simp]:
  "input (process_refineRes f g x) = refine_resource f g (input x)"
  by (induct x ; simp add: resource_par_def)
lemma process_refineRes_output [simp]:
  "output (process_refineRes f g x) = refine_resource f g (output x)"
  by (induct x ; simp add: resource_par_def)
lemma process_refineRes_primitives:
  " primitives (process_refineRes f g x)
  = map (\<lambda>(ins, outs, l, m). (refine_resource f g ins, refine_resource f g outs, l, m))
        (primitives x)"
  by (induct x ; simp add: image_Un)
lemma process_refineRes_valid [simp]:
  "valid x \<Longrightarrow> valid (process_refineRes f g x)"
  by (induct x ; simp)

section\<open>List-based Composition Actions\<close>

text\<open>
  We define functions to compose a list of processes in sequence or in parallel.
  In both cases these associate the binary operation to the right, and for the empty list they both
  use the identity process on the @{const Empty} resource.
\<close>

text\<open>Compose a list of processes in sequence\<close>
primrec seq_process_list :: "('a, 'b, 'l, 'm) process list \<Rightarrow> ('a, 'b, 'l, 'm) process"
  where
    "seq_process_list [] = Identity Empty"
  | "seq_process_list (x # xs) = (if xs = [] then x else Seq x (seq_process_list xs))"

lemma seq_process_list_input [simp]:
  "xs \<noteq> [] \<Longrightarrow> input (seq_process_list xs) = input (hd xs)"
  by (induct xs) simp_all

lemma seq_process_list_output [simp]:
  "xs \<noteq> [] \<Longrightarrow> output (seq_process_list xs) = output (last xs)"
  by (induct xs) simp_all

lemma seq_process_list_valid:
  " valid (seq_process_list xs)
  = ( list_all valid xs
    \<and> (\<forall>i :: nat. i < length xs - 1 \<longrightarrow> output (xs ! i) = input (xs ! Suc i)))"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (simp add: hd_conv_nth nth_Cons')
       (metis Suc_less_eq Suc_pred diff_Suc_1' length_greater_0_conv zero_less_Suc)
qed

lemma seq_process_list_primitives [simp]:
  "primitives (seq_process_list xs) = concat (map primitives xs)"
  by (induct xs) simp_all

text\<open>We use list-based sequential composition to make generated code more readable\<close>
lemma seq_process_list_code_unfold [code_unfold]:
  "Seq x (Seq y z) = seq_process_list [x, y, z]"
  "Seq x (seq_process_list (y # ys)) = seq_process_list (x # y # ys)"
  by simp_all

text\<open>Resource refinement can be distributed across the list being composed\<close>
lemma seq_process_list_refine:
  "process_refineRes f g (seq_process_list xs) = seq_process_list (map (process_refineRes f g) xs)"
  by (induct xs ; simp)

text\<open>Compose a list of processes in parallel\<close>
primrec par_process_list :: "('a, 'b, 'l, 'm) process list \<Rightarrow> ('a, 'b, 'l, 'm) process"
  where
    "par_process_list [] = Identity Empty"
  | "par_process_list (x # xs) = (if xs = [] then x else Par x (par_process_list xs))"

lemma par_process_list_input [simp]:
  "input (par_process_list xs) = foldr (\<odot>) (map input xs) Empty"
  by (induct xs) simp_all

lemma par_process_list_output [simp]:
  "output (par_process_list xs) = foldr (\<odot>) (map output xs) Empty"
  by (induct xs) simp_all

lemma par_process_list_valid [simp]:
  "valid (par_process_list xs) = list_all valid xs"
  by (induct xs ; clarsimp)

lemma par_process_list_primitives [simp]:
  "primitives (par_process_list xs) = concat (map primitives xs)"
  by (induct xs ; simp)

text\<open>We use list-based parallel composition to make generated code more readable\<close>
lemma par_process_list_code_unfold [code_unfold]:
  "Par x (Par y z) = par_process_list [x, y, z]"
  "Par x (par_process_list (y # ys)) = par_process_list (x # y # ys)"
  by simp_all

text\<open>Resource refinement can be distributed across the list being composed\<close>
lemma par_process_list_refine:
  "process_refineRes f g (par_process_list xs) = par_process_list (map (process_refineRes f g) xs)"
  by (induct xs ; simp)

subsection\<open>Progressing Both Non-deterministic Branches\<close>

text\<open>
  Note that validity of @{const Opt} requires that its children have equal outputs.
  However, we can define a composition template that allows us to optionally compose processes with
  different outputs, producing the non-deterministic combination of those outputs.
  This represents progressing both branches of a @{const NonD} resource without merging them.
\<close>
fun OptProgress :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b, 'l, 'm) process"
  where "OptProgress p q =
  Opt (Seq p (InjectL (output p) (output q)))
      (Seq q (InjectR (output p) (output q)))"

text\<open>
  The result takes the non-deterministic combination of the children's inputs and produces the
  non-deterministic combination of their outputs, and it is valid whenever the two children are
  valid.
\<close>
lemma [simp]:
  shows OptProgress_input: "input (OptProgress x y) = NonD (input x) (input y)"
    and OptProgress_output: "output (OptProgress x y) = NonD (output x) (output y)"
    and OptProgress_valid: "valid (OptProgress x y) = (valid x \<and> valid y)"
  by simp_all

section\<open>Primitive Action Substitution\<close>

text\<open>
  We define a function to substitute primitive actions within any process composition.
  The target actions are specified through a predicate on their parameters.
  The replacement composition is then a function of those primitives.
\<close>
primrec process_subst ::
  " (('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow>
    (('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> ('a, 'b, 'l, 'm) process) \<Rightarrow>
    ('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b, 'l, 'm) process"
  where
    "process_subst P f (Primitive a b l m) = (if P a b l m then f a b l m else Primitive a b l m)"
  | "process_subst P f (Identity a) = Identity a"
  | "process_subst P f (Swap a b) = Swap a b"
  | "process_subst P f (Seq p q) = Seq (process_subst P f p) (process_subst P f q)"
  | "process_subst P f (Par p q) = Par (process_subst P f p) (process_subst P f q)"
  | "process_subst P f (Opt p q) = Opt (process_subst P f p) (process_subst P f q)"
  | "process_subst P f (InjectL a b) = InjectL a b"
  | "process_subst P f (InjectR a b) = InjectR a b"
  | "process_subst P f (OptDistrIn a b c) = OptDistrIn a b c"
  | "process_subst P f (OptDistrOut a b c) = OptDistrOut a b c"
  | "process_subst P f (Duplicate a) = Duplicate a"
  | "process_subst P f (Erase a) = Erase a"
  | "process_subst P f (Represent p) = Represent (process_subst P f p)"
  | "process_subst P f (Apply a b) = Apply a b"
  | "process_subst P f (Repeat a b) = Repeat a b"
  | "process_subst P f (Close a b) = Close a b"
  | "process_subst P f (Once a b) = Once a b"
  | "process_subst P f (Forget a) = Forget a"

text\<open>If no matching target primitive is present, then the substitution does nothing\<close>
lemma process_subst_no_target:
  "(\<And>a b l m. (a, b, l, m) \<in> set (primitives x) \<Longrightarrow> \<not> P a b l m) \<Longrightarrow> process_subst P f x = x"
  by (induct x, auto)

text\<open>If a process has no primitives, then any substitution does nothing on it\<close>
lemma process_subst_no_prims:
  "primitives x = [] \<Longrightarrow> process_subst P f x = x"
  by (fastforce intro: process_subst_no_target)

text\<open>
  If the replacement process does not change the inputs, then input is preserved through the
  substitution
\<close>
lemma process_subst_input [simp]:
  "(\<And>a b l m. P a b l m \<Longrightarrow> input (f a b l m) = a) \<Longrightarrow> input (process_subst P f x) = input x"
  by (induct x) simp_all

text\<open>
  If the replacement additionally does not change the outputs, then the output is also preserved
  through the substitution
\<close>
lemma process_subst_output [simp]:
  assumes "\<And>a b l m. P a b l m \<Longrightarrow> input (f a b l m) = a"
      and "\<And>a b l m. P a b l m \<Longrightarrow> output (f a b l m) = b"
    shows "output (process_subst P f x) = output x"
  using assms by (induct x) simp_all

text\<open>
  If the replacement is additionally valid for every target, then validity is preserved through the
  substitution
\<close>
lemma process_subst_valid [simp]:
  assumes "\<And>a b l m. P a b l m \<Longrightarrow> input (f a b l m) = a"
      and "\<And>a b l m. P a b l m \<Longrightarrow> output (f a b l m) = b"
      and "\<And>a b l m. P a b l m \<Longrightarrow> valid (f a b l m)"
    shows "valid (process_subst P f x) = valid x"
  using assms by (induct x) simp_all

text\<open>
  Primitives after substitution are those that didn't satisfy the predicate and anything that was
  introduced by the function applied on satisfying primitives' parameters.
\<close>
lemma process_subst_primitives:
  " primitives (process_subst P f x)
  = concat (map
      (\<lambda>(a, b, l, m). if P a b l m then primitives (f a b l m) else [(a, b, l, m)]) (primitives x))"
  by (induct x) simp_all

text\<open>After substitution, no target action is left unless some replacement introduces one\<close>
lemma process_subst_targets_removed:
  assumes "\<And>a b l m a' b' l' m'.
    \<lbrakk>(a, b, l, m) \<in> set (primitives x); P a b l m; (a', b', l', m') \<in> set (primitives (f a b l m))\<rbrakk>
    \<Longrightarrow> \<not> P a' b' l' m'"
    \<comment> \<open>For any target primitive of the process, no primitive in its replacement is also a target\<close>
      and "(a, b, l, m) \<in> set (primitives (process_subst P f x))"
    shows "\<not> P a b l m"
  using assms
proof (induct x)
  case (Primitive x1 x2 x3 x4)
  then show ?case
    by simp (smt (verit) empty_iff empty_set fst_conv primitives.simps(1) set_ConsD snd_conv)
next case (Seq x1 x2) then show ?case by simp blast
next case (Par x1 x2) then show ?case by simp blast
next case (Opt x1 x2) then show ?case by simp blast
next case (Represent x) then show ?case by simp
next case (Identity x) then show ?case by simp
next case (Swap x1 x2) then show ?case by simp
next case (InjectL x1 x2) then show ?case by simp
next case (InjectR x1 x2) then show ?case by simp
next case (OptDistrIn x1 x2 x3) then show ?case by simp
next case (OptDistrOut x1 x2 x3) then show ?case by simp
next case (Duplicate x) then show ?case by simp
next case (Erase x) then show ?case by simp
next case (Apply x1 x2) then show ?case by simp
next case (Repeat x1 x2) then show ?case by simp
next case (Close x1 x2) then show ?case by simp
next case (Once x1 x2) then show ?case by simp
next case (Forget x) then show ?case by simp
qed

text\<open>Process substitution distributes over list-based sequential and parallel composition\<close>
lemma par_process_list_subst:
  "process_subst P f (par_process_list xs) = par_process_list (map (process_subst P f) xs)"
  by (induct xs ; simp)

lemma seq_process_list_subst:
  "process_subst P f (seq_process_list xs) = seq_process_list (map (process_subst P f) xs)"
  by (induct xs ; simp)

section\<open>Useful Notation\<close>

text\<open>
  We set up notation to easily express the input and output of a process.
  We use two bundle: including one introduces the notation, while including the other removes it.
\<close>
abbreviation spec :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> bool"
  where "spec P a b \<equiv> input P = a \<and> output P = b"

bundle spec_notation
begin
notation spec ("(_): (_) \<rightarrow> (_)" [1000, 60] 60)
end

bundle spec_notation_undo
begin
no_notation spec ("(_): (_) \<rightarrow> (_)" [1000, 60] 60)
end

text\<open>Set up notation bundles to be imported in a controlled way, along with inverses to undo them\<close>

text\<open>
  We also set up infix notation for sequential and parallel process composition.
  Once again, we use two bundles to add and remove this notation.
  In this case that is even more useful, as out parallel composition notation overrides that of
  @{const Shuffle}.
\<close>
bundle process_notation
begin
no_notation Shuffle (infixr "\<parallel>" 80)
notation Seq (infixr ";;" 55)
notation Par (infixr "\<parallel>" 65)
end

bundle process_notation_undo
begin
notation Shuffle (infixr "\<parallel>" 80)
no_notation Seq (infixr ";;" 55)
no_notation Par (infixr "\<parallel>" 65)
end

end
