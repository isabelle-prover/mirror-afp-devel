(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "In-Out Parameters, Abstracting Pointers to Values"

theory In_Out_Parameters_Ex imports "AutoCorres" 
begin

consts abs_step:: "word32 \<Rightarrow> word32 \<Rightarrow> bool"

subsection \<open>Overview\<close>

text \<open>We introduce a new phase in AutoCorres to replace pointer parameters by \<^emph>\<open>in/out parameters\<close>:
Instead of passing a pointer into a function we pass the initial value of the pointer 
(by dereferencing the pointer) into the function and return the value at the end of the function
as additional output. E.g. a function \<^verbatim>\<open>void inc(unsigned *n)\<close> becomes \<^verbatim>\<open>unsigned inc(unsigned n)\<close>.
The initial motivation for this phase was to get rid of explicit pointers to local variables 
and replace them by ordinary values instead.
This conversion has two main aspects:
\<^item> Function signatures may change: pointer parameters become value parameters and
  the function may return the value of the pointer at the end as an additonal
  return value (tupled with the ordinary return value). Functions with side effects on the heap
  may become pure functions on values by this transformation.
\<^item> As a result of the first transformation, pointers to local variables may be eliminated 
  and be replaced by bound variables. This means that \<^const>\<open>stack_heap_state.with_fresh_stack_ptr\<close> 
  disappears.

The new phase is called \<^emph>\<open>IO\<close> and is placed between L2 and HL. This means local variables are
already represented as bound variables in L2 and we still operate on a monolithic heap.

\<close>

subsection \<open>Building Blocks\<close>

text \<open>
What ingredients do we need for the abstraction relation in the refinement proof?
\<^item> Heaps: As we eliminate pointers, the original function manipulates the heap more 
  often then the resulting function. So we need a notion to relate the heap states and keep track
  of the relevant pointers. As the stack of local variable pointers is also modelled in the heap
  the stack free locations are also of interest. The heaps of the original and the resulting
  program may differ in these locations. The heap value of a stack free location should be 
  irrelevant for the program.

\<^item> Function signatures: The function signature changes, pointer parameters become ordinary values,
  the return value is tupled with output parameters.

In the following we refer to the original state (containing the heap) as \<^term>\<open>s\<close> and the
resulting / abstract state as \<^term>\<open>t\<close>.
As I first idea we want to relate states \<^term>\<open>s\<close> and \<^term>\<open>t\<close> such that the heaps are the
same except for some pointers we want to eliminate and the stack free locations. It would be natural
to describe this as a relation. However, it turns out that dealing with relations within the
refinement proof are hard to make admissible in order to support recursive functions. Having a
abstraction / lifting function (instead of a relation) from \<^term>\<open>s\<close> to \<^term>\<open>t\<close> makes admissibility
straightforward.

As a prerequisite we encourage the reader to consider the documentation about
pointers to local variables: \<^file>\<open>pointers_to_locals.thy\<close>
\<close>

context heap_state
begin
subsubsection \<open>\<^const>\<open>frame\<close>\<close>

text \<open>We want to express that certain portions of the heap (typing and values) are 'irrelevant',
in particular regarding (free) stack space. The notion of 'irrelevant' is a bit vague, it means
that the behaviour of the resulting program does not depend on those locations and also that it does not 
modify those locations. Moreover, we prefer an abstraction function rather than an 
relation between states to avoid admissibility issues for refinement.
The central property is \<^term>\<open>t = frame A t\<^sub>0 s\<close>, for \<^term>\<open>A\<close> being a set of addresses and
\<^term>\<open>t\<close>, \<^term>\<open>t\<^sub>0\<close> and \<^term>\<open>s\<close> being states. Think of \<^term>\<open>A\<close> as the set of \<^emph>\<open>allocated\<close> addresses
containing those pointers we want to \<^emph>\<open>abstract\<close> aka. eliminate.\<close>

thm frame_def

text \<open>
The standard use case we have in mind is @{term "A \<inter> stack_free (htd s) = {}"}, hence
@{prop "A - stack_free (htd s) = A"}, but nevertheless the intuition is:
\<^item> stack free typing from \<^term>\<open>s\<close> is preserved, the framed sate has at least as many stack free
  addresses as the original one. So we can simulate any stack allocation.
\<^item> heap values for stack free and \<^term>\<open>A\<close> are taken from reference state \<^term>\<open>t\<^sub>0\<close>, this
  captures that we do not depend on the original values in \<^term>\<open>s\<close> for those addresses.
\<^item> typing for allocations in \<^term>\<open>A\<close> is taken from reference state \<^term>\<open>t\<^sub>0\<close>, this captures
  that we do not depend on the original typing in \<^term>\<open>s\<close> for those addresses.

By taking the same reference state \<^term>\<open>t\<^sub>0\<close> to frame two states \<^term>\<open>s\<close> and \<^term>\<open>s'\<close>,
we can express that the 'irrelevant' parts of the heap did not change in the respective
framed states \<^term>\<open>frame A t\<^sub>0 s\<close> and \<^term>\<open>frame A t\<^sub>0 s'\<close>.
\<close>

subsubsection \<open>\<^const>\<open>rel_alloc\<close>, \<^const>\<open>rel_stack\<close>, \<^const>\<open>rel_sum_stack\<close>\<close>

text \<open>The core invariant between the states that is maintained by the refinement is
\<^term>\<open>rel_alloc \<S> M A t\<^sub>0 s t\<close>:
\<^item> \<^term>\<open>\<S>\<close> is a static set of addresses containing the stack. Stack allocation and stack release
  are contained within \<^term>\<open>\<S>\<close>.
\<^item> \<^term>\<open>M\<close> is the set of addresses that might be modified by the original program.
\<^item> \<^term>\<open>A\<close> is the set of addresses that are eliminated (abstracted) in the resulting program. Another 
  good intuition about the set \<^term>\<open>A\<close> is that the original function might read from and depend on 
  those addresses but the resulting function does not. Moreover, the resulting function does not
  change any of heap locations in \<^term>\<open>A\<close>. The resulting function is agnostic to those locations. 
  It neither reads nor modifies them.
  For any heap valuation of \<^term>\<open>A\<close> the abstract function simulates the original one.
\<^item> \<^term>\<open>t\<^sub>0\<close> is the reference state explained above.
\<^item> \<^term>\<open>s\<close> is the state of the original program
\<^item> \<^term>\<open>t\<close> is the state of the resulting program.
\<close>

thm rel_alloc_def [of \<S> M A t\<^sub>0]

text \<open>
The properties of \<^const>\<open>rel_alloc\<close> are:
\<^item> \<^term>\<open>t = frame A t\<^sub>0 s\<close>, the resulting heap in \<^term>\<open>t\<close> is the same as the original in \<^term>\<open>s\<close>, 
  except for the addresses in \<^term>\<open>A\<close> and the stack free space.
\<^item> \<^term>\<open>stack_free (htd s) \<subseteq> \<S>\<close>: The stack free space is contained in \<^term>\<open>\<S>\<close>.
\<^item> \<^term>\<open>stack_free (htd s) \<inter> A = {}\<close>: We only want to eliminate properly allocated pointers, which
  are not contained in the stack free space.  
\<^item>  \<^term>\<open>stack_free (htd s) \<inter> M = {}\<close>: We only mention properly allocated pointers to be modified. 
  Modifications within the stack free space are irrelevant, as they are abstracted by the framing
  anyways.
\<close>
text \<open>
For an original function \<^term>\<open>f\<close> and the abstract aka. lifted function \<^term>\<open>g\<close> the refinement
property has the following shape:
\<^prop>\<open>rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))\<close>

Note that the output relation of \<^const>\<open>refines\<close> relates both the resulting states and return
values to each other. The return values of the error monad are related by \<^const>\<open>rel_sum_stack\<close>, taking a
relation \<^term>\<open>L\<close> for error values (\<^term>\<open>Inl\<close>) and the \<^term>\<open>R\<close> for normal termination (\<^term>\<open>Inr\<close>).

\<close>
thm rel_sum_stack_def
thm rel_stack_def [of \<S> M1 A s t\<^sub>0 "rel_sum_stack L R"]

text \<open>Consider the output states \<^term>\<open>s'\<close> and \<^term>\<open>t'\<close> and the output values \<^term>\<open>v\<close> and \<^term>\<open>w\<close> 
for the original and the abstracted function. Then we have:
\<^item> \<^term>\<open>rel_xval_stack L R (hmem s') v w\<close>: The result values are related, (see below).
\<^item> \<^term>\<open>rel_alloc \<S> M1 A t\<^sub>0 s' t'\<close>: In particular \<^term>\<open>t' = frame A t\<^sub>0 s'\<close>. Note that we use
   the same \<^term>\<open>A\<close> and the same reference state \<^term>\<open>t\<^sub>0\<close> as for the initial states. So this means
   that the abstract program \<^term>\<open>g\<close> does not change the heap values and typing in \<^term>\<open>A\<close> and does
   not depend on the values. 
\<^item> \<^term>\<open>equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s)\<close>: The original program only modifies
   pointers contained in \<^term>\<open>M1\<close> or in the stack free portions of the heap 
    (e.g. by nested function calls).
\<^item> \<^term>\<open>equal_upto M1 (htd s') (htd s)\<close>: Changes to the heap typing of the original program 
   are confined within set \<^term>\<open>M1\<close>.
\<^item> \<^term>\<open>equal_on \<S> (htd s') (htd s)\<close>: The stack typing of the original program remains unchanged.
  Note that it might change temporarily by nested function calls but the stacking discipline
  restores the state.
By construction we have \<^term>\<open>M1 \<subseteq> M\<close>.
\<close>

paragraph \<open>Stacking pointers: \<^const>\<open>rel_singleton_stack\<close>, \<^const>\<open>rel_push\<close>\<close>

text \<open>
The relation on the output value captures the idea that portions of the heap are stacked / tupled 
into result values. On the boundaries of a function the relation on error values \<^term>\<open>L\<close> is always the
trivial \<^term>\<open>\<lambda>_. (=)\<close>. Errors are terminal as there is no exception handling in C. Within
the boundaries of a function there can be more complex relations reflecting the nesting of
break / continue / return and goto. 
For ordinary values the values of pointers are tupled by \<^const>\<open>rel_singleton_stack\<close>, in case 
the original function returned no result (void), or nested by  \<^const>\<open>rel_push\<close> in case the
original function returned some result.
\<close>
thm rel_singleton_stack_def
thm rel_push_def
text \<open>
 A typical relation is \<^term>\<open>R = rel_singleton_stack p\<close> for some pointer \<^term>\<open>p\<close>. This means
that the abstract value can be obtained by looking into the heap at pointer \<^term>\<open>p\<close>:
\<^term>\<open>rel_singleton_stack p h () v\<close> means that \<^term>\<open>v = h_val h p\<close>. The heap of the original program
 is propagated down the into the relations.
Similar \<^term>\<open>rel_push p (\<lambda>_. (=)) h x (v, x)\<close> relates the result value \<^term>\<open>x\<close> to the tuple
\<^term>\<open>(v, x)\<close> where \<^term>\<open>v = h_val h p\<close>. Note that \<^term>\<open>rel_push\<close> can be nested represent multiple
output parameters.
Depending on the role of the pointers there are additional assumptions about the pointers, 
in particular things like \<^term>\<open>ptr_span p \<subseteq> A\<close> or  \<^term>\<open>ptr_span p \<subseteq> M\<close> and disjointness properties 
like \<^term>\<open>distinct_sets [ptr_span p, ptr_span q]\<close>.
\<close>

subsubsection \<open>\<^const>\<open>IOcorres\<close>\<close>

text \<open>
There is an additional predicate \<^const>\<open>IOcorres\<close> which represents the result of the refinement
proof in the canonical autocorres ideom that is used within the other phases. This form
is what is expected when constructing the final theorem combining all autocorres layers
@{thm ac_corres_chain_sims}. The \<^term>\<open>refines\<close> version and the \<^term>\<open>IOcorres\<close> version can
be converted into each other by @{thm ac_corres_chain_sims}.
\<close>
thm IOcorres_def
thm IOcorres_refines_conv
thm ac_corres_chain_sims
end

install_C_file "in_out_parameters.c"


subsection \<open>Options\<close>

text \<open>
To control the in/out- parameter abstraction there are two options of autocorres:
\<^item> \<open>skip_io_abs\<close> a boolean which is \<open>true\<close> by default. This skips the complete phase for all 
  functions.
\<^item> \<open>in_out_parameters\<close> which takes a list of in-out specifications for functions. As soon
  as there is at least one specification present the phase is enabled (taking
  precedence over \<open>skip_io_abs\<close>. 

So to properly enable the IO phase you have two main choices to specify what should be done
either in @{command "init-autocorres"} or subsequent calls to @{command autocorres}. You can
only disable option \<open>skip_io_abs\<close> in @{command "init-autocorres"} and then provide the
individual options for \<open>in_out_parameters\<close> in subsequent @{command autocorres} invocations, or
you can already define all \<open>in_out_parameters\<close> already in @{command "init-autocorres"}.

More details on the options are provided in the following examples.
\<close>

subsection \<open>Examples\<close>


init-autocorres [ in_out_parameters = 
    compare(cmp:out) and
    inc(y:in_out) and
    inc_int(y:in_out) and
    dec(y:in_out) and
    swap(x:in_out, y:in_out) and
    swap_pair(x:in_out, y:in_out) and
    call_inc_ptr(p: in_out) and
    inc_twice(y:in_out) and
    inc2(y:in_out, z:in_out) and 
    heap_inc2_part(z:in_out) and
    heap_inc2_part_swap(y:in_out) and
    safe_add(result: in_out) and
    inc_pair(p:in_out) and
    get_arr_idx(arr:"in") and
    get_pair_arr_idx_second(arr:"in") and
    inc_pair(p:in_out) and
    xyz(x:in_out) and
    resab(res:in_out) and
    abcmp(cmpRst:in_out) and
    out(out:out) and
    out2(out:in_out) and
    out_seq(out:out) and
    inc_loop (x:"in", y:in_out) and
    call_inc_int_other(m: in_out) and
    inc_int_no_exit(y:in_out) and
    call_inc_int_other_mixed(m: in_out) and
    inc_int2(y:in_out, z:in_out) and
    call_inc_int2(n:in_out) and
    call_inc_int_pair(p:in_out) and
    call_inc_int_array(p:in_out) and
    call_compare_ptr(m:"out") and
    mixed_global_local_inc(q:"in_out") and
    g1(out:"in_out") and
    set_void(p:"data") and
    set_void2(p:"data") and
    set_byte(p:"data") and
    read_char(p:in_out, len: in_out) and
    goto_read_char1(p:in_out) and
    goto_read_char5(elem: "in"),
    in_out_globals =
      keep_inc_global_array
      inc_global_array
      keep_inc_global_array2
      inc_global_array2
      call_keep_inc_global_array
      call_inc_global_array
      mixed_global_local_inc shuffle global_array_update
      read_char call_read_char call_read_char_loop 
      goto_read_char1 goto_read_char2 goto_read_char3 goto_read_char4 goto_read_char5,
    ignore_addressable_fields_error, (* FIXME *)
    addressable_fields = 
      pair.first 
      pair.second 
      array.elements
      int_pair.int_first
      int_pair.int_second
     (* int_array.int_elements*)
(*
FIXME: open_types seems to have an issue that
lemma "typ_uinfo_t TYPE(32 signed word[3]) = typ_uinfo_t (TYPE(32 word[3])))"

*)
   ]"in_out_parameters.c"


text \<open>In option \<open>in_out_parameters\<close> you provide a parameter specification for the functions
you want to abstract. 
The parameter specs following the parameter name are
\<^item> \<open>in\<close>: pointer is only used as input to the function. The referenced value does not change
  during the function call.
\<^item> \<open>out\<close>: the pointer is only used to output a result from the function. The referenced value at
   the beginning is irrelevant, the abstracted function should return the referenced value at
   the end of the original function.
\<^item> \<open>in_out\<close> the pointer is used to input a value and to return a result.

When no specification is given for a function, the list is considered empty. This means that
the signature of the function shall not be changed by the abstraction. Pointer parameters in 
the original function stay pointer parameters in the resulting function.
Note that this has a quite different effect from just skipping the phase, as autocorres is still attempting
to do a proper refinement proof. More details are provided by the examples.
\<close>

locale keep_globals = in_out_parameters_global_addresses +
  assumes keep_global_array: "{ptr_val global_array ..+128} \<subseteq> \<G>"
begin
lemma global_array_contained1:
  assumes i_bound: "i < 12" 
  shows "ptr_span (global_array +\<^sub>p (int i)) \<subseteq> \<G>"
proof -
  have "ptr_span (global_array +\<^sub>p (int i)) \<subseteq> {ptr_val global_array ..+128}"
    using i_bound
    apply (clarsimp simp add: ptr_add_def intvl_def)
    subgoal for k
    apply (rule exI [where x= "i * 4 + k"])
      by force
    done
  with keep_global_array show ?thesis by blast
qed

lemma gobal_array_contained2[polish]:
  assumes i_bound: "numeral i < (12::nat)"
  shows "ptr_span (global_array +\<^sub>p (numeral i)) \<subseteq> \<G>"
  using global_array_contained1
  by (metis i_bound of_nat_numeral)

end

autocorres  [
    (* base_locale=keep_globals *) (* experimental *)
    ts_force nondet = shuffle] "in_out_parameters.c"

context in_out_parameters_all_corres
begin

thm io_corres
thm ts_def
term ptr_valid
subsubsection \<open>\<^const>\<open>inc'\<close>\<close>

text \<open>

The function \<^verbatim>\<open>inc\<close> increments the value which is passed as a pointer \<^verbatim>\<open>y\<close>.
\<^verbatim>\<open>
void inc (unsigned* y) {
  *y = *y + 1;
}
\<close>

When we abstract this function to have an in-out parameter instead, we obtain a function like:

\<^verbatim>\<open>
void inc (unsigned y) {
  y = y + 1;
  return y;
}
\<close>
Note that this is now a pure function, that does no longer depend on the heap. This is
also the final output of autocorres in @{thm inc'_def}:
\<close>
thm inc'_def

text \<open>
Let us zoom into the refinement step from L2 to IO.
\<close>
thm l2_inc'_def
thm io_inc'_def
text \<open>
Note that the type of parameter \<^term>\<open>y\<close> changes from a pointer type to a value type. Here
is the generated refinement theorem.
\<close>
thm io_inc'_corres 
lemma "c_guard y \<Longrightarrow>
  distinct_sets [ptr_span y] \<Longrightarrow>
  ptr_span y \<subseteq> A \<Longrightarrow>
  ptr_span y \<subseteq> M \<Longrightarrow>
  globals.rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow>
  refines 
    (l2_inc' y) 
    (io_inc' (h_val (hrs_mem (t_hrs_' s)) y)) s t 
    (globals.rel_stack \<S> (ptr_span y) A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (rel_singleton_stack y)))"
  by (rule io_inc'_corres)

text \<open>
Parameter \<open>y\<close> was specified as \<open>in_out\<close>. So function \<^const>\<open>io_inc'\<close> becomes the actual value
of the pointer passed in: \<^term>\<open>(h_val (hrs_mem (t_hrs_' s)) y)\<close>. To discharge the \<^term>\<open>c_guard y\<close>
guards within the body of \<^const>\<open>l2_inc'\<close> we need the assumption that the guard holds at the beginning.
As we attempt to abstract pointer \<open>y\<close> we have its pointer span included in set \<^term>\<open>A\<close>. Moreover,
the content of pointer \<open>y\<close> is modified by \<^const>\<open>l2_inc'\<close> hence it appears in \<^term>\<open>M\<close> as well
as explicit in the final relation \<^term>\<open>globals.rel_stack\<close>. 
Pointer parameters are assumed to be distinct. As we have only one parameter the assumption trivially
\<^term>\<open>distinct_sets [ptr_span y]\<close> holds. 
Note that set \<^term>\<open>A\<close> is only constrained by \<^term>\<open>ptr_span y \<subseteq> A\<close>. So we could instantiate it
with the universal set \<^term>\<open>UNIV::addr set\<close>. Recalling the meaning of \<^term>\<open>A\<close> this means that
the resulting function \<^term>\<open>io_inc'\<close> is a pure function, in the sense that it does not depend
on the heap anymore. The relation for the termination with \<^verbatim>\<open>exit\<close> is \<^term>\<open>rel_exit (\<lambda>_ _ _. False)\<close>, 
which expresses
that this path is unreachable for the current function. The function will never terminate with
\<^verbatim>\<open>exit\<close>.
\<close>

subsubsection \<open>\<^const>\<open>call_inc_parameter'\<close>\<close>

text \<open>
Next we look at a function that calls our previously defined integer function on a pointer
to its parameter.
\<^verbatim>\<open>
unsigned call_inc_parameter(unsigned n) {
  inc(&n);
  return(n);
}
\<close>
After autocorres the function is just a mere wrapper to the increment function
\<close>
thm call_inc_parameter'_def

text \<open>Here are the relevant definitions and the IO refinement theorem.\<close>
thm l2_call_inc_parameter'_def
thm io_call_inc_parameter'_def
thm io_call_inc_parameter'_corres [no_vars]

thm io_call_inc_parameter'_corres
lemma "distinct_sets ([]::addr set list) \<Longrightarrow>
  globals.rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow>
  refines 
     (l2_call_inc_parameter' n) 
     (io_call_inc_parameter' n) s t
     (globals.rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (\<lambda>_. (=))))"
  by (rule io_call_inc_parameter'_corres)

text \<open>Note that here we do not have any assumption on the set \<^term>\<open>A\<close> and the modified variables
 in the final state are empty. This is because we eliminate a pointer to a temporary stack variable that
 is out of scope after the function and in the beginning of the function it is part of the \<^term>\<open>stack_free\<close> 
 space. 

\<close>


subsubsection \<open>const\<open>keep_inc'\<close>\<close>

text \<open>Now let us consider a copy of the increment function were we do not convert to in out parameters
but leave it as it is. Unsurprisingly, the resulting function still operates on pointers.\<close>
thm keep_inc'_def

text \<open>Let us look into the IO corres phase.\<close>
thm l2_keep_inc'_def
thm io_keep_inc'_def
thm io_keep_inc'_corres

lemma "distinct_sets [ptr_span y] \<Longrightarrow>
  ptr_span y \<inter> A = {} \<Longrightarrow>
  ptr_span y \<inter> stack_free (hrs_htd (t_hrs_' s)) = {} \<Longrightarrow> \<comment> \<open>FIXME: redundant assumption?, follows from the next ones\<close>
  globals.rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow>
  ptr_span y \<subseteq> M \<Longrightarrow>
  refines 
    (l2_keep_inc' y) 
    (io_keep_inc' y) s t
    (globals.rel_stack \<S> (ptr_span y) A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (\<lambda>_. (=))))"
  by (rule io_keep_inc'_corres) 
text \<open>As pointer \<open>y\<close> is an allocated pointer that we do not abstract it should not belong to
\<^term>\<open>A\<close> and must not collide with \<^term>\<open>stack_free\<close> space. As we might modify the pointer it
is contained in \<^term>\<open>M\<close> as well as the final modifies set.

Note that the bodies of \<^const>\<open>io_keep_inc'\<close> and \<^const>\<open>l2_keep_inc'\<close> are equivalent but the
refinement statement is not a trivial statement and in particular is not the same as when
skipping the IO corres phase. For example from the refinement statement we can derive that
any heap location different from \<^term>\<open>ptr_span y\<close> is unchanged. 

Next let's look what happens when we call this function on a local parameter.
\<close>

subsubsection \<open>\<^const>\<open>keep_call_inc_parameter'\<close>\<close>

thm keep_call_inc_parameter'_def
thm io_keep_call_inc_parameter'_def
thm l2_keep_call_inc_parameter'_def
thm io_keep_call_inc_parameter'_corres [no_vars]

lemma "distinct_sets ([]::addr set list) \<Longrightarrow>
  globals.rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow>
  refines 
    (l2_keep_call_inc_parameter' n) 
    (io_keep_call_inc_parameter' n) s t
    (globals.rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (\<lambda>_. (=))))"
  by (rule io_keep_call_inc_parameter'_corres)

text \<open>The local variable pointer is still present in the final function. Still the refinement
statement indicates that we have a `pure' functions, as we do not have constraints on \<^term>\<open>A\<close>
and also do not modify anything. The notion of pure we use here, is that the function does
not depend on proper heap pointers. The \<^term>\<open>stack_free\<close> space that we temporarily use is
excluded by our definitions of \<^const>\<open>globals.frame\<close>, \<^const>\<open>globals.rel_alloc\<close> and \<^const>\<open>globals.rel_stack\<close>.
\<close>

subsubsection \<open>\<^const>\<open>safe_add'\<close>\<close>

text \<open>This function is an example of an arithmetic function that checks for overflows. The
status of the check is the return value and the result of the operation is passed via pointer.
We make an in-out parameter for the result. So the final function returns a tuple of the
result value and the status (\<^const>\<open>rel_push\<close> in the refinement statement).
\<close>
thm safe_add'_def
thm l2_safe_add'_def
thm io_safe_add'_def
thm io_safe_add'_corres


subsubsection \<open>Recursion\<close>

thm l2_fac'.simps
thm io_fac'.simps
thm io_fac'_corres

thm l2_even'.simps l2_odd'.simps
thm io_even'.simps io_odd'.simps
thm io_even'_corres io_odd'_corres

subsubsection \<open>\<^const>\<open>swap'\<close>\<close>

text \<open>We abstract a function that swaps the values referenced by two input pointers by a function that
takes the values and returns the swapped values (as a pair). Note that in the
refinement statement we assume disjointness of the input pointers. The swap function would still 
be correct if the pointers are equal. To generalise the refinement proofs to `disjoint or equal' 
inputs is left as future work. \<close>

thm swap'_def
thm l2_swap'_def
thm io_swap'_def
thm io_swap'_corres

subsubsection \<open>Out parameters\<close>

text \<open>The function \<open>compare\<close> has an mere 'out' parameter. Until phase L2 the function has three parameters,
after phase IO the function only has two parameters.\<close>

thm l2_compare'_def
thm io_compare'_def
thm compare'_def

thm l2_call_compare'_def
thm io_call_compare'_def
thm call_compare'_def


subsubsection \<open>Pointers to compound types (structs / arrays)\<close>

text \<open>Here are some examples of function that work on (parts) of a compound type.\<close>


thm get_arr_idx'_def
thm l2_get_arr_idx'_def
thm io_get_arr_idx'_def

thm inc_pair'_def
thm l2_inc_pair'_def
thm io_inc_pair'_def

subsubsection \<open>Misc\<close>

thm wa_def
thm ts_def
thm io_corres

subsection \<open>Handling \<^verbatim>\<open>exit\<close> in function calls\<close>

text \<open>When we call a function that was refined by in-out-parameters there are various cases
we have to consider, e.g. do we pass in a heap pointer or a local pointer, do we eliminate the
local pointer or keep it? 
In general when we pass in a pointer that is not supposed to be eliminated as an in-out parameter
we first pass in the dereferenced value and after the function returns we take the value from the embellished
result and assign it to the pointer. So the pointer assignment that would take place
in the middle of the called function in the original program, is moved outside of the call in the
refined program. After this the heaps of the original program and the refined program are in sync
again at the pointer.
To establish the heap refinement it turns out that we also have to bring the heaps in sync 
again even if the function terminates with \<^verbatim>\<open>exit\<close>. We catch the \<^verbatim>\<open>exit\<close>, update the heap and then
re-throw the \<^term>\<open>exit\<close>. So the called function also returns embellished exit values which
hold the value of the relevant pointers. This extra work is a little annoying as the \<^verbatim>\<open>exit\<close> terminates the
complete program and usually we do not catch an \<^verbatim>\<open>exit\<close>. So this step might introduce
\<^const>\<open>L2_catch\<close> to wrap up the procedure call. Note that this is currently the only remaining
use case for \<^const>\<open>L2_catch\<close>, the other occurrences of \<^const>\<open>L2_catch\<close> were already transformed
to \<^const>\<open>L2_try\<close> as post processing in phase L2 when we move from `flat' exception handling to 
`nested' exception handling.

\<close>

term inc_int'
thm inc_int'_def
term call_inc_int_ptr'
thm call_inc_int_ptr'_def

subsection \<open>Global Heap Pointers\<close>

text \<open>
A core part of the IO phase is to keep track of pointers and in particular to do some 
bookkeeping of the parts of the heap that might get modified. This analysis and bookkeeping is
focused around the pointers that are visible in the signature of a function. This fails short
as soon as pointers to global heap are used within the body of a function, which are not
mentioned in the function signature. To handle some common use cases with global heap
we have a mechanism to over-approximate the impact of a function on the heap by referring to a
static set \<^term>\<open>\<G>\<close> of addresses that should not be abstracted by the IO phase. We can 
annotate a function to make use of this mechanism by mentioning them in @{command "init-autocorres"}
with the option \<^verbatim>\<open>in_out_globals\<close>. 
For the refinement statement we assume that
\<^item> \<^prop>\<open>\<G> \<inter> A = {}\<close>: pointers in \<^term>\<open>\<G>\<close> are not supposed to be abstracted, and
\<^item> \<^prop>\<open>\<G> \<subseteq> M\<close>: the function might modify any global variable.

Within the body of such a function (marked with  option \<^verbatim>\<open>in_out_globals\<close>), 
whenever a pointer is used which does not occur in the signature
as pointer parameter and is specified otherwise we assume that
this pointer a global pointer and assert this formally by adding
a guard \<^prop>\<open>ptr_span x \<subseteq> \<G>\<close>. If a function has multiple pointer parameters we also assert
disjointness of pointers.
\<close>

thm io_keep_inc_global_array'_corres
thm io_keep_inc_global_array'_def
thm l2_keep_inc_global_array'_def

thm io_inc_global_array'_corres
thm io_inc_global_array'_def
thm l2_inc_global_array'_def

thm io_inc_global_array2'_corres
thm io_inc_global_array2'_def
thm l2_inc_global_array2'_def
thm ac_corres

text \<open>Note that a function can also have both in-out parameters and \<^verbatim>\<open>in_out_globals\<close>.\<close>

thm io_read_char'_corres
thm io_read_char'_def
thm l2_read_char'_def

thm io_call_read_char'_corres
thm io_call_read_char'_def
thm l2_call_read_char'_def

thm io_call_read_char_loop'_corres
thm io_call_read_char_loop'_def
thm l2_call_read_char_loop'_def


subsection \<open>Disclaimer / Caution\<close>

text \<open>As we have seen in the examples the refinement theorems can contain assumptions on the
input pointers, in particular disjointness assumptions between different pointer parameters and 
also disjointness of pointer parameters to complete memory areas like \<^term>\<open>stack_free\<close>. When
a function is called these assumptions have to be discharged. When these pointer parameters are
eliminated (replaced by in-out value parameters) the assumptions disappear. So when you work
on the final output of autocorres you know nothing about pointers or disjointness.

In case a local pointer is eliminated these assumptions are be discharged locally as an intermediate
step in the proof. So this use case is fine.
However, if the function is called on a heap pointer these assumptions are propagated to the caller. So
the assumptions move up the call stack and might end up as implicit hidden assumptions on your 
toplevel functions (API).

Rule of thumb: In case your toplevel API function has more then one pointer parameter 
don't specify any in-out parameters on that function to avoid implicit assumptions.

\<close>

subsection \<open>Implementation Aspects\<close>

text \<open>
The proof of the refinement theorem requires to keep track of various pointers and changes
the signature of functions, including extending plain return values to tuples.
We decided to make a rather explicit forward proof for this, to keep tight control of the
various aspects. We make heavy use of ML antiquotations to match and build cterms.
An obstacle here is that the state record \<^typ>\<open>globals\<close>. which holds the heap,
is not yet defined but is only present as a locale. So our code is implemented within
the locale @{locale stack_heap_state}. We have introduced the concept of
\<^emph>\<open>interpretation data\<close> (c.f. \<^file>\<open>../lib/ml-helpers/interpretation_data.ML\<close>) to get hold
of the interpretation we are interested in. 
The data is initialised in \<^file>\<open>../AutoCorres.thy\<close> as declaration within @{locale stack_heap_state}.
In particular this allows us to match against and build heap lookup and heap update expressions.

The interface is via @{ML \<open>In_Out_Parameters.operations\<close>}. This takes the morphism of the
interpretation as an argument to derive the instance we are interested in.
Note that we have crafted the main functions to benefit from the eager evaluation of ML.
In particular @{ML \<open>In_Out_Parameters.operations\<close>} takes the morphism \<open>phi\<close> as its only parameter
and thus the instances of the main functions are only evaluated once.
\<close>
end


subsection \<open>pointer-parameters as data\<close>

text \<open>In a case where a pointer is not used to access the heap (e.g., \<open>set_void\<close>), the
  "modifies" part of the corres theorem should be empty.
  Otherwise functions like \<open>set_byte\<close>, that pass "arbitrarily" computed pointers fail to get
  IO-lifted.
  We enforce this by declaring pointer parameters as "data" in the \<open>in_out_parameters\<close> option of
  autocorres.

  Future work: Automate this analysis to infer which pointer-parameters are treated as pure data.
  \<close>
context io_corres_set_void begin

lemma "distinct_sets ([]::addr set list)
  \<comment> \<open>should be able to get rid of this assumption, too (for multiple parameters)\<close> \<Longrightarrow>
globals.rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow>
refines (l2_set_void' p) (io_set_void' p) s t
 (globals.rel_stack \<S> {} A s t\<^sub>0
   (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (\<lambda>_. (=))))"
  by (rule io_set_void'_corres)
end
context io_corres_set_void2 begin
thm io_set_void2'_corres
end
context io_corres_set_byte begin
thm io_set_byte'_corres
end

subsection \<open>Future work / Open Ends\<close>
text \<open>
\<^item> Support function pointers
\<^item> support functions that might modify the heap typing (e.g. via \<open>exec_concrete\<close>)
  currently our \<open>rel_alloc\<close> / \<open>rel_stack\<close> setup enforces that heap typing does not change at all
  this is to restrictive. Before we had that heap typing does not change in \<^term>\<open>\<S>\<close> which was
  too weak to modify the \<open>A\<close> frame to handle invocations on heap pointers. I guess a good
  approximation would be to say that heap typing is unchanged on all relevant addresses:
            \<open>\<S> \<union> A \<union> M\<close>
  Including \<open>M\<close> might be too restrictive, e.g. consider an alloc function that zeros some 
  memory and adapts the heap-typing.
\<^item> Refined treatment of \<open>in_out_globals\<close>: allow the user to add a guard that is inserted
  in front of the abstract program.
  E.G. locale for procedure: \<open>ptr_span (global_array + MAX_IDX) \<subseteq> \<G>\<close>
    + a Guard depending on a parameter \<open>idx\<close>, e.g. \<open>idx < MAX_IDX\<close>. Then we can automatically
    discharge local guards like \<open>ptr_span (global_array + idx) \<subseteq> \<G>\<close>. Not sure if this is 
  useful though
\<^item> Cleanup unused \<open>Generic_Data\<close> that was replaced by interpretation data
\<^item> Remove struct-rewrite step from Heap Lifting. As we normalise pointers to root pointers in
  L2-Opt the pointers should already be in normal form and struct-rewrite does nothing.
\<^item> Add sanity checks to \<open>in_out\<close> specs, especially if parameter names actually occur in signature
\<^item> Remove redundant assumptions for keep parameters:
  \<open>ptr_span y \<inter> stack_free (hrs_htd (t_hrs_' s)) = {} \<Longrightarrow>
  globals.rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow>
  ptr_span y \<subseteq> M \<Longrightarrow> ...\<close>
  \<^item> The first one can be derived from the following ones

\<^item> Peephole: remove \<open>ptr_disjoint\<close> of singletons
\<^item> Peephole simplification, especially Guard True. Not really necessary, will disappear in hl
  anyways.
\<^item> Eliminate pointers to global variables: When a pointer to a global variable is only used
  as a \<open>in_out parameter\<close> it would be nice to abstract it to a record field in \<open>lifted_globals\<close>  (or
  to something similar, i.e. lookup / update function in the heap with disjointnes and
  commutation of updates for other globals )
\<^item> Support more relaxed disjoint assumptions, especially \<open>disjoint_or_eq\<close>, 
  e.g. swap also works if the input pointers are equal.
  \<^item> All `keep` pointers are currently assumed disjoint and also are in the modifies set. We could
    be more relaxed here.
\<^item> HL phase has some explicit references to phase L2 instead of abstract \<open>prev_phase\<close> (probably related
  to function pointers)
\<^item> Would be nice if synthesize rules would also participate in thm, and add / del stuff
  like \<open>named_rules\<close>
\<close>

end
