(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Pointers to Local Variables"

theory pointers_to_locals imports "AutoCorres" 
begin

install_C_file "pointers_to_locals.c"
init-autocorres [addressable_fields = pair.first buffer.buf "32 word[3]"]"pointers_to_locals.c"
autocorres [no_heap_abs = inc_untyp]"pointers_to_locals.c"

text \<open>
This story began with the desire to support "pointers to local variables".
The idea to support "pointers to local variables" might be quite fearful as it covers lots of
use cases. When trying to literally support pointers to local variables 
(uniform with heap pointers) one has to answer questions about the memory layout 
of heap and stack, how to ensure that those regions are disjoint, what happens if we run out of 
stack space, how do we make sure that there is no dangling pointers to a stack-frame that 
is already popped from the stack etc.

So let us make a step back and ask ourselves for which C-idiomatic use cases are 
pointers to local variables actually used. C does only support call-by-value. So pointers
are sometimes used to model call-by-reference semantics, for input as well as output parameters.
Especially, the use case of an additional output parameter (besides the regular return value) is
often implemented as a pointer parameter. An alternative might be to return a tuple encoded as
a structure instead. But as there are no ad hoc tuples in C, this requires the 
boilerplate to define an auxiliary structure type. So typically a pointer parameter is used
instead.
 
Here an example of a integer addition with overflow check. The return value is used for the
status, the actual result is returned as a pointer parameter.
\<^verbatim>\<open>
int add_check(int* result, int a, int b)
{
    *result = a + b;
    if(a > 0 && b > 0 && *result < 0)
        return -1;
    if(a < 0 && b < 0 && *result > 0)
        return -1;
    return 0;
}
\<close>
A call to the function could be the following with a local variable for the result.
\<^verbatim>\<open>
  int res, status;
  status = add_check(&res, 2, 3)
\<close>

Here \<^verbatim>\<open>res\<close> is an output parameter. If C would support tuples we might have code like:

\<^verbatim>\<open>
int add_check(int a, int b)
{
    int result = a + b;
    if(a > 0 && b > 0 && *result < 0)
        return (-1, resut);
    if(a < 0 && b < 0 && *result > 0)
        return (-1, result);
    return (0, result);
}
\<close>

\<^verbatim>\<open>
  int res, status;

  (status, res) = add_check(2, 3)
\<close>

Another use case is to have in input / output parameter implemented by a pointer parameter.

\<^verbatim>\<open>
void inc(int *a)
{
  (*a)++;
}

int x = 42;
inc(&x);
\<close>

This could be also modelled as explicit input and output:

\<^verbatim>\<open>
int inc(int a)
{
  return (a++);
}

int x = 42;
x = inc(x);
\<close>


So one general idea is to model those kind of pointer-parameters as explicit input / output parameters.
From a pattern like:
\<^verbatim>\<open>
int f(int *p1, ..., int * p_n, int a1, ..., int a_m) {
  ... (*p1) ...
  ... (*p_i) ...
  return res;
}

r = f(q1,..., q_n, b1, ..., b_m)
\<close>

We make

\<^verbatim>\<open>
(int * int ... * int) f(int p1, ..., int p_n, int a1, ..., int a_m) {
  ... p1 ...
  ... p_i ...
  return (res, p1, ... p_n);
}

(r, q1, ..., q_n) = f(q1,..., q_n, b1, ..., b_m)
\<close>



In which cases is such a model faithful? 
Different behaviours might occur, when pointer-parameters are aliased. Moreover, the translation
scheme only works out if the body of the function only uses the dereferenced pointer variables,
i.e. \<^verbatim>\<open>*p_i\<close> to obtain the value or perform an update, and does not actually use the literal
address value stored in the variable. E.g. it does not make things like \<^verbatim>\<open>p1 = p2\<close> or stores
the pointer value in some global data structure. 
All examples we have seen so far are benign with this respect, as there was only one 
pointer-variable involved, and we only used it to dereference it.

What about this swap function:
\<^verbatim>\<open>
void swap1(int* p, int* q) {
  int tmp = *p;
  *p = *q;
  *q = tmp;
}

int a = 1; int b =2;
swap1(&a, &b);
/* a = 2, b = 1 */
\<close>

\<^verbatim>\<open>
(int * int) swap2(int p, int q) {
  int tmp = p;
  p = q;
  q = tmp;
  return (p, q);
}

int a = 1; int b = 2;
(a, b) = swap2(a, b);
/* a = 2, b = 1 */
\<close>

These two swap functions behave the same, even if the parameters would alias. But in 
general aliasing is problematic. 

\<^verbatim>\<open>
void inc_both1(int* p, int* q) {
  *p = *p + 1;
  *q = *q + 1;
}

int x = 2;
void inc_both1(&x, &x);

/* x = 4 */
\<close>

\<^verbatim>\<open>
(int * int) inc_both2(int p, int q) {
  p = p + 1;
  q = q + 1;
  return (p, q);
}

int x = 2;
(x, x) = inc_both2(&x, &x);

/* x = 3 */
\<close>

Whats the relevant difference between the increment and the swap example?
In the swap example, we never read from a pointer-parameter after any pointer-parameter
was assigned to. So an update within the function might not alter the values we read via any
pointer-parameter.
\<close>

subsection \<open>Design choices\<close>

text \<open>
C does not distinguish pointers to local variables from heap pointers they are all the same.
E.g. the increment functions above could be applied to a heap location as well as a stack location.
Moreover, in the context of systems programming it is common that low-level code explicitly
deals with heap-layout and pointer values and "tricks" like storing some flags as bits in
the pointer values themselves are often used.
That is why we aim for an uniform model for stack and heap pointers and don't want to 
impose assumptions on the layout.

Whenever a function creates a pointer to a local variable, we model it as part of the heap. Core
ideas:
\<^item> As part of ordinary heap-typing, we track free stack locations by a distinguished 
  C type @{typ stack_byte}. All addresses with that type are considered free stack location.
\<^item> Additionally to the typing information with @{typ stack_byte} 
  (that denotes free stack space) We have a fixed set of addresses \<^term>\<open>\<S>\<close> that describe all the stack space 
  (free and allocated). Note that the set \<^term>\<open>\<S>\<close> does not depend on the state. The dynamic
  aspects are modelled within the heap typing.
\<^item> As prelude in a function that needs pointers to local variables  
  we allocate the variable in the heap, by non-deterministically 
  retyping a region of free stack space that fits: We retype from @{typ stack_byte} to the
  type we allocate.  
\<^item> All accesses / updates to the variable within the function are modelled indirectly via the
  pointer
\<^item> As postlude of the function we again retype the stack space as free.


Observations:
\<^item> Ordinary C functions, that do not have an AUX-UPDATE on the heap-type also do not mess around
  with the stack as they do not change heap-typing. So stack-space is preserved
  when calling a function.
\<^item> Prelude / postlude ensures that the stack typing is the same after a function call to
  a function that has pointers to local variables. 
\<close>

subsubsection \<open>Stack Allocation\<close>

text \<open>The central definition for stack allocation is @{const stack_allocs} describing the set of
possible pointers and modified heap type descriptions:

\<^term>\<open>(p::'a::mem_type ptr, d') \<in> stack_allocs n \<S> TYPE('a::mem_type) d\<close>
\<close>

thm stack_allocs_def

text \<open>
After such an allocation we know that:
\<^item> Pointer \<^term>\<open>p\<close> is a root pointer with the expected type in the new heap type description \<^term>\<open>d'\<close>.
\<^item> The allocated addresses are within set \<^term>\<open>\<S>\<close>.
\<^item> The new heap typing \<^term>\<open>d'\<close> is obtained from the original heap typing \<^term>\<open>d\<close> by retyping 
  addresses of \<^typ>\<open>stack_byte\<close> to the type of the pointer \<^term>\<open>p\<close>. The address of pointer \<^term>\<open>p\<close>
  denotes the start the retyped region. The parameter \<^term>\<open>n\<close> can be used to allocate a
  consecutive range of pointers in one step.

Stack allocation might fail in the sense that the resulting set of \<^const>\<open>stack_allocs\<close> can be
empty. In Simpl we then fail in the terminal fault state reporting \<^const>\<open>StackOverflow\<close>.
In the autocorres monad we currently have decided to ignore possible stack overflows. We simply
assume that stack allocation succeeds and does not return an empty set.
\<close>

subsubsection \<open>Stack Release\<close>

text \<open>The counter part to the stack allocation above is \<^term>\<open>stack_releases n p d'\<close>. 
\<close>

thm stack_releases_def

text \<open>
There is no non-determinism here. It is a plain function retyping back to \<^typ>\<open>stack_byte\<close>.
\<close>

subsubsection \<open>Stack discipline\<close>

text \<open>
We encapsulate the stacking discipline of allocation / release in some functions in 
the various layers.
\<close>

paragraph \<open>Simpl\<close>
text \<open>
In Simpl we have the command \<^term>\<open>With_Fresh_Stack_Ptr n init c\<close> where
\<^item> \<^term>\<open>n\<close> denotes the number of consecutive pointers we want to allocate, typically \<^term>\<open>1\<close>. This number was
  introduced to allocate local arrays and obtain pointers to the elements. However, it turns out
  that allocating an array pointer \<^typ>\<open>('a['b]) ptr\<close> instead is sufficient. Hence the parameter is
  actually always \<^term>\<open>1\<close>. 
\<^item> \<^term>\<open>init s\<close> returns a set of initial values from which we non-deterministically choose one.
  In case the addressed local variable is a function parameter this is a singleton set containing
  the value of the argument. In case of an ordinary local variable this is either the the universal set
  of all possible values (if uninitialized) or a singleton set of the initialisation value.
\<^item> \<^term>\<open>c\<close> expects a fresh pointer \<^term>\<open>p\<close> and then yields a Simpl command of the body.

The idea is simple, we first allocate a pointer \<^term>\<open>p\<close> with \<^const>\<open>stack_allocs\<close>, then initialise
the fresh heap location according to \<^term>\<open>init\<close> then execute the body \<^term>\<open>c p\<close> and finally
release the stack pointer again.
\<close>
thm globals.With_Fresh_Stack_Ptr_def
term stack_heap_state.With_Fresh_Stack_Ptr

text \<open>
A central role of the definition is the \<^const>\<open>DynCom\<close> statements, which is the means of Simpl
to bind certain execution points and provide state dependent commands. As the body of a \<^const>\<open>DynCom\<close> 
always depends on the complete state (and not such a thing like the pointer \<^term>\<open>p\<close> ) we use
 the function \<^const>\<open>allocated_ptrs\<close> calculate the fresh pointer from the typing information.
\<close>

thm allocated_ptrs_def
thm stack_allocs_allocated_ptrs

text \<open>
Note that \<^term>\<open>Spec\<close> might fail if the resulting set is empty,  
which is exposed to the failure \<^const>\<open>StackOverflow\<close> of the command.
\<close>

paragraph \<open>L1 / L2\<close>

text \<open>In both L1 and  L2 we use \<^term>\<open>globals.with_fresh_stack_ptr n init f\<close>, where \<^term>\<open>n\<close> as well
as\<^term>\<open>init\<close> are just the same as in Simpl and \<^term>\<open>f\<close> is a monadic computation depending on
the fresh pointer \<^term>\<open>p\<close>.\<close>

term globals.with_fresh_stack_ptr
thm globals.with_fresh_stack_ptr_def
term stack_heap_state.with_fresh_stack_ptr

text \<open>
In contrast to Simpl we assume that stack allocation succeeds by using \<^const>\<open>assume_result_and_state\<close>.
\<close>

subsubsection \<open>HL / Split Heap\<close>

text \<open>
In the split heap model there is no singleton heap anymore. Hence we introduce a family
of functions depending on the type that is allocated.
\<close>

term heap_w32.with_fresh_stack_ptr
thm heap_w32.with_fresh_stack_ptr_def
term heap_w32.guard_with_fresh_stack_ptr
thm heap_w32.guard_with_fresh_stack_ptr_def
term heap_w32.assume_with_fresh_stack_ptr
thm heap_w32.assume_with_fresh_stack_ptr_def
term typ_heap_typing.with_fresh_stack_ptr
term typ_heap_typing.guard_with_fresh_stack_ptr
term typ_heap_typing.assume_with_fresh_stack_ptr

text \<open>While stack allocation remains the same upon stack release some more work has to
be done in order to make the simulation work.

In the monolitic heap the stack release of a pointer \<^term>\<open>p\<close> immediately results in
 \<^term>\<open>plift (h, stack_releases n p d') p = None\<close>. So the simulation demands
 \<^term>\<open>the_default c_type_class.zero (plift (h, stack_releases n p d') p) = zero\<close>.
\<^footnote>\<open>c.f. \<^file>\<open>open_struct.thy\<close> for details on heap lifting simulation\<close>.

So to simulate this in the split heap we explicitly zero out the memory. 
Moreover, for the simulation to work we have to argue that the stack release did not mess up with
any of the other split heaps. This argument can be given if know that
pointer \<^term>\<open>p\<close> is still a valid root pointer before we do the release. As we know that \<^term>\<open>p\<close> is a
valid root pointer immediately after the allocation we have to establish that this is still true
at stack release. Most C function do not alter the heap typing at all. So it can easily
be shown that \<^term>\<open>f \<bullet> s ?\<lbrace>\<lambda>r t. lifted_globals.unchanged_typing_on \<S> s t\<rbrace>\<close> holds and thus that \<^term>\<open>p\<close> is
still a valid root pointer after executing \<^term>\<open>f\<close>.
In case we cannot automatically proof the preservation of typing information, we enforce
that \<^term>\<open>p\<close> is still a valid root pointer by inserting a guard. So for code that changes
the heap typing in more involved ways the argument is left for the user to prove.
\<close>

thm lifted_globals.unchanged_typing_on_def
term heap_typing_state.unchanged_typing_on

text \<open>Some syntax\<close>

term "PTR_VALID(32 word)"
term "IS_VALID(32 word) s"
term "IS_VALID(32 word) s p"


context ts_definition_inc
begin
thm ts_def
end

text \<open>Pointer to an uninitialized local variable.\<close>
context call_inc_local_uninitialized_impl
begin
thm call_inc_local_uninitialized_body_def
end

context ts_definition_call_inc_local_uninitialized
begin
thm ts_def
end

text \<open>Pointer to an initialized local variable.\<close>
context ts_definition_call_inc_local_initialized
begin
thm ts_def
end

text \<open>Pointer to parameter.\<close>
context ts_definition_call_inc_parameter
begin
thm ts_def
end

text \<open>When we cannot prove that the heap typing is unchanged we fall back
to \<^const>\<open>heap_w32.guard_with_fresh_stack_ptr\<close> instead of 
 \<^const>\<open>heap_w32.assume_with_fresh_stack_ptr\<close>
\<close>
context ts_definition_call_inc_untyp
begin
thm ts_def
end

text \<open>Nested pointers among the phases.\<close>

context call_inc_nested_impl
begin
thm call_inc_nested_body_def
end

context l1_definition_call_inc_nested
begin
thm l1_def
end

context l2_definition_call_inc_nested
begin
thm l2_def
end

context hl_definition_call_inc_nested
begin
thm hl_def
end

context wa_definition_call_inc_nested
begin
thm wa_def
end

context ts_definition_call_inc_nested
begin
thm ts_def
end

text \<open>Global variable\<close>
context ts_corres_call_inc_global
begin
thm ts_def
end

text \<open>Local array variable.\<close>
context ts_definition_call_inc_array
begin
thm ts_def
end

text \<open>Local structure variable.\<close>

context ts_definition_call_inc_first
begin
thm ts_def
end

text \<open>Local array in structure variable.\<close>
context ts_definition_call_inc_buffer
begin
thm ts_def
end

text \<open>Mutual recursion and pointer to local variables.\<close>

context l2_definition_odd_even
begin
thm unchanged_typing
end
context ts_corres_odd_even
begin
thm ts_def
end


subsubsection \<open>Proof rules for \<open>runs_to_vcg\<close>\<close>


context pointers_to_locals_all_corres begin

(* stack_ptr_simps discards the most common proof obligations generated by runs_to_vcg when used 
   with pointers to stack locations *)

thm stack_ptr_simps

lemma "(call_inc_local_initialized') \<bullet> s \<lbrace> \<lambda> r t. t = s \<and> r = Result 43 \<rbrace>"
  apply (unfold call_inc_local_initialized'_def inc'_def)
  apply runs_to_vcg
  apply (auto simp: stack_ptr_simps comp_def) (* comp_def needs to be added explicitly *)
  done

lemma "(call_inc_local_uninitialized') \<bullet> s \<lbrace> \<lambda> r t. t = s \<and> r = Result 42 \<rbrace>"
  apply (unfold call_inc_local_uninitialized'_def inc'_def)
  apply runs_to_vcg
  apply (auto simp: stack_ptr_simps comp_def)
  done

lemma "(call_inc_parameter' n) \<bullet> s \<lbrace> \<lambda> r t. t = s \<and> r = Result (n + 1) \<rbrace>"
  apply (unfold call_inc_parameter'_def inc'_def)
  apply runs_to_vcg
  apply (auto simp: stack_ptr_simps comp_def)
  done

end

subsection \<open>Open Ends / TODOs\<close>



text \<open>
There are not yet any user level proof rules 
for \<^const>\<open>heap_w32.guard_with_fresh_stack_ptr\<close> and  \<^const>\<open>heap_w32.assume_with_fresh_stack_ptr\<close> to include 
with @{method runs_to_vcg}.
Note that there are a lot of theorems on the primitives \<^const>\<open>stack_allocs\<close> and \<^const>\<open>stack_releases\<close>.
\<close>
thm stack_allocs_cases
thm stack_allocs_ptr_valid_cases
thm stack_releases_ptr_valid_cases
thm stack_releases_ptr_valid_cases1

subsubsection \<open>Value parameters aka. In-Out parameters\<close>

text \<open>
Now that we have proper pointers to local variables there is room for further abstractions, 
motivated by the prominent use cases described in the beginning. Those use cases 
suggest that in a lot of cases one can completely get rid of stack allocation / release by introducing value 
parameters: Instead of just passing a pointer value into the function, one 
passes in the actual (dereferenced) value and tuples the return value of the function with the final (dereferenced) 
value of that parameter.

It turns out that the core transformation here is not so much about pointers to local
variables but more on transforming functions from passing in a pointer parameter to another 
function value parameters. 
This part of the transformation is independent of the question heap pointer vs. stack pointer. 
After this transformation is done for the body of a function
which allocates a stack pointer, the actual address of the stack pointer becomes meaningless as it
is only used in "dereferenced form". So we can remove the stack allocation / stack release and
replace it by an ordinary local variable. 

See \<^file>\<open>In_Out_Parameters_Ex.thy\<close> for more information.
\<close>

end
