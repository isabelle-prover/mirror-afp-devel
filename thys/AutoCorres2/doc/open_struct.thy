(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Pointers into Structures in Split Heap \label{sec:open_struct}\<close>

theory open_struct
  imports "AutoCorres"
begin

subsection \<open>Overview\<close>

text \<open>
Heap lifting in AutoCorres transforms the monolithic byte-level heap \<^typ>\<open>heap_mem\<close> with explicit
term level heap type description \<^typ>\<open>heap_typ_desc\<close> and typing constraints, like \<^const>\<open>c_guard\<close>,
 \<^const>\<open>h_t_valid\<close> and \<^term>\<open>d \<Turnstile>\<^sub>t p\<close> to a more abstract split heap model with implicit HOL-typing.
The major advantage of the split heap model is that, updates to one particular heap do
not affect all other distinct heaps, removing the obligation to explicitly take care about aliasing.
Aliasing between different heaps is ruled out by the model already.

The question that arises is on which granularity do we split the byte-level heap?
The original AutoCorres splitted at the granularity of types. Each distinct c-type is mapped into
a separate heap. In that model you can still have intra-type aliasing (i.e. pointers of the
same type can alias), but no inter-type aliasing (i.e. pointers of different type are distinct, and
 cannot alias). As an example a pointer to a list structure refers to a different (split) heap as
a pointer to a tree structure. So when a function modifies lists, no pointer to a tree is affected.

Of course not every C-program can be represented in this split-heap model. In those cases
the abstraction fails.
In particular think of a low-level memory allocator, that allocates some raw-bytes and
delivers a void-pointer, that is then retyped to point to the actual structure. To be able
to combine those byte-level functions with high-level typed functions (in the split heap) one
can switch between both layers of abstraction by \<^const>\<open>exec_concrete\<close> and \<^const>\<open>exec_abstract\<close>.
The good thing is that this gives us a very expressive tool to switch between byte-level and
typed view. We can do the specification and proofs of different parts of the program on
the adequate level and still combine the results. But switching between the layers can be
tedious and thus should be limited to the low-level functions that really inherently need
byte-level reasoning.

Unfortunately the type granularity of the split heaps also rules out programs dealing with
pointers into a structure. For example a structure containing a \<open>int\<close> field \<open>count\<close> cannot pass a
\<open>int\<close> pointer to that field \<open>count\<close> to a another function, that might update it.
The complete structure has a separate
(split) heap that is distinct from the heap containing \<open>int\<close>s. This would mean that we
have to resort to the byte-level heap to reason about those functions.

We extended the split heap model to support this common use-case. The core idea is that
in addition to split heaps on the granularity of types you can also specify split heaps on the
granularity of structure fields. Conceptually you 'open' the structure into its 
components (aka. fields) and each field gets a separate heap. Additionally you can specify which 
fields should be \<^emph>\<open>addressable\<close> and thus shared. In the example you can specify that \<open>count\<close> is addressable,
so it is represented within the same heap as all other \<open>int\<close>. This means that an \<open>int\<close> pointer can
now point to a plain \<open>int\<close> or to a \<open>count\<close> field within a structure. You explicitly allow
this limited inter-type aliasing on \<open>int\<close> pointers. All other fields that are not
explicitly marked as \<^emph>\<open>addressable\<close> still have their own heap and thus cannot alias with another
pointer of the same field type. Note that mainly for performance reasons we actually avoid to 
have a separate heap for each single field but try to minimise the number of heaps by clustering the 
fields that are treated the same. Some more details on this construction are below. 
\<close>

subsection \<open>Example Program and some Intuition\<close>

text \<open>We illustrate the approach with the following example specifying some structures,
with addressable and non-addressable fields. Note that for an addressable field that is
 of an array type, each element of the array is considered to be addressable.
\<close>

install_C_file "open_struct.c"

text \<open>\<close>

declare [[show_types=false, show_sorts=false,
 verbose = 0, verbose_timing = 0, ML_print_depth = 1000, goals_limit = 20]]

init-autocorres [addressable_fields =
  inner.fld1
  inner.fld2
  outer.inner
  outer_array.inner_array
  array.elements
  other.fy
  two_dimensional.matrix
  data_struct1.d1.y1
  data_struct1.d1.y2
  data_struct1.d1.y3
  data_struct1.d1.y4
  data_struct1.d2
  data_struct2.d
  data_array.array,
 single_threaded  (* turn on to see timing info *)] "open_struct.c"

text \<open>\<close>

autocorres open_struct.c

text \<open>
Which split heaps are generated? Each split heap is a component of the record \<^typ>\<open>lifted_globals\<close>.
\<close>

print_record lifted_globals

  text \<open>

Structure \<open>closed\<close> does not have any addressable field. So there is a separate heap for that
component \<^const>\<open>closed_C\<close>.

Structure \<open>inner\<close> has three \<open>unsigned\<close> fields \<^const>\<open>fld1_C\<close>, \<^const>\<open>fld2_C\<close> and \<^const>\<open>fld3_C\<close>,
The first two fields are addressable whereas the third one is not.
This means that the first two fields are put into the same common heap for unsigned integers
\<^const>\<open>heap_w32\<close> whereas the third field is stored in a dedicated heap for all remaining fields
 \<^const>\<open>dedicated_heap_inner_C\<close>.

We use the following nomenclature to distinguish the various kinds of split heaps and types:
\<^item> closed type or structure: There is no addressable field within the type / structure,
    e.g. \<^typ>\<open>closed_C\<close>.
\<^item> open type or structure: There is at least one addressable field within the type / structure,
    e.g. \<^typ>\<open>inner_C\<close>.
\<^item> atomic heap: Heap for a closed type, or a common heap that might be nested in an open structure.
    e.g. \<^const>\<open>heap_closed_C\<close>.
\<^item> dedicated heap: Internal heap for all non-addressable fields of an open type,
    e.g. \<^const>\<open>dedicated_heap_inner_C\<close>. These dedicated heaps are used for the construction of a derived heap.
\<^item> derived heap: Heap for an open type / structure. The name 'derived' indicates that it is not a fundamental heap
    but a composition of several common heaps and a dedicated heap,
    e.g. \<^const>\<open>inner_C\<close>
\<^item> fundamental heap: those heaps that are directly present in the new global state \<^typ>\<open>lifted_globals\<close>.
  These are atomic heaps, and dedicated heaps.
\<^item> virtual heap: heaps that represent the user level view. They are directly visible in
  the program after heap-lifting. This excludes dedicated heaps, which non-the-less may be used in the
  model as representation of that type.

Dedicated heaps play a special role, as they are subsumed within derived heaps. In a sense they are
not part of the 'API' for split heaps: After heap lifting the resulting program only directly
mentions atomic, common or derived heaps. Nevertheless dedicated heaps are important for the
construction of derived heaps and might show up after unfolding the definitions for derived heaps.

Also dedicated heaps may be used by the user as the actual heap for a specific type. Only the dedicated
heaps and the atomic heaps commute, the derived heaps do not necessary commute with each other as
they might have common components that alias each other.
\<close>

subsection \<open>Background\<close>

text \<open>
The starting point for the split heap abstraction is still the
unified memory model (UMM) by Harvey Tuch
(@{url \<open>https://trustworthy.systems/publications/papers/Tuch%3Aphd.pdf\<close>}). The UMM provides
the general concept of \<^class>\<open>c_type\<close> to convert between a byte-list representations of
C values to abstract HOL-types. It also provides an explicit notion of typing and what a
well-typed byte level heap is (with respect to a heap type description). With these notions
in place one can describe the set of valid pointers for a C program. The model is quite elaborate
and respects the potential nesting of structures. A well-typed pointer to a structure in the heap
gives rise to a bunch of other valid sub-pointers, pointing to sub-fields, which again could point to
a nested structure.
In the UMM, array types are modelled as a special case of a structure, where each index corresponds to
an artificial field, where the field name is a unary encoding of the index. Hence, for most of
the explanation in this file it is sufficient to elaborate on structures. 
The main limitation of the UMM is that it does not handle unions.

For the original split heap version of AutoCorres
@{url \<open>https://trustworthy.systems/publications/nicta_full_text/8758.pdf\<close>}, David Greenaway
put a simplified layer on top of the UMM focusing only on the root-pointers of a structure,
ignoring any nested pointers to a field. This provides a split heap abstraction on
the granularity of types.

The new split heap model takes an intermediate view. For closed structures it coincides with
the original split heap model. Only root-pointers to a closed structure are valid.
In addition for open structures also the nested pointers to addressable fields are welcome and valid.
This flexibility allows the user to carefully open up the structures only as far as needed.
Note the trade-off between expressibility and "proof-burden" of open structures. Aliasing is
by construction ruled out for distinct split heaps, but has to be dealt with explicitly on
the user level for common heaps.

To allow this flexibility some existing notions where slightly refined and some notions where
introduced.
\<close>

subsubsection \<open>Footprints and valid pointers\<close>

text \<open>
The central typing judgement of UMM is \<^const>\<open>h_t_valid\<close>, with infix syntax \<^term>\<open>d,g \<Turnstile>\<^sub>t p\<close>, meaning
pointer \<^term>\<open>p\<close> is valid with respect to heap type description \<^term>\<open>d\<close> and a guard \<^term>\<open>g\<close>.
The default guard is \<^const>\<open>c_guard\<close>, ensuring that the pointer is aligned, is not NULL and that
the referenced value fits into the address space, meaning that the addresses of the
individual bytes do not overflow the address space. This instantiation with \<^const>\<open>c_guard\<close>
is abbreviated with \<^term>\<open>d \<Turnstile>\<^sub>t p\<close>.
\<close>
thm c_guard_def
thm TypHeap.h_t_valid_def
thm h_t_valid_valid_footprint

text \<open>
The judgement \<^term>\<open>d,g \<Turnstile>\<^sub>t p\<close> also ensures that the footprint is valid:
\<^term>\<open>valid_footprint d (ptr_val p) (typ_uinfo_t TYPE('a::c_type))\<close>.
Note that \<^term>\<open>p\<close> is a typed pointer, carrying the (phantom) type of the value it points
to \<^term>\<open>p::'a ptr\<close>. This type annotation is no longer present in \<^const>\<open>valid_footprint\<close> which
only talks about the address of the pointer \<^const>\<open>ptr_val\<close> and relates it to a type tag
via \<^const>\<open>typ_uinfo_t\<close>.
\<close>
thm valid_footprint_def
text \<open>
Without going into details of the definition of \<^const>\<open>valid_footprint\<close> we get guarantees for
all nested pointers of the structure which also have \<^const>\<open>valid_footprint\<close>. Moreover, what
we do not know is whether the pointer \<^term>\<open>p\<close> is itself a nested pointer of some enclosing
structure.

To get the additional knowledge that term \<^term>\<open>p\<close> is a root pointer, meaning it is not
enclosed in a bigger structure, we have the notion \<^const>\<open>valid_root_footprint\<close>.
This notion was refined from the original version of AutoCorres \<^const>\<open>valid_simple_footprint\<close>
to get the important property that every \<^const>\<open>valid_root_footprint\<close> is
indeed also a \<^const>\<open>valid_footprint\<close>.
\<close>
thm valid_root_footprint_valid_footprint
text \<open>Also for all types that fit into the address space we can go from \<^const>\<open>valid_root_footprint\<close>
 to \<^const>\<open>valid_simple_footprint\<close>. The restriction on the address space size follows from the
 implicit property of the legacy\<^const>\<open>valid_simple_footprint\<close>: The first byte and all the rest have a
 different tag, so there must not be a complete wrap around in the address space.
\<close>
thm valid_simple_footprint_size_td
thm valid_root_footprint_valid_simple_footprint

text \<open>
The corresponding judgment to \<^term>\<open>d \<Turnstile>\<^sub>t p\<close> for root pointers is
\<^term>\<open>root_ptr_valid d p\<close>. It implies \<^term>\<open>c_guard p\<close> as well as
\<^term>\<open>valid_root_footprint d (ptr_val p) (typ_uinfo_t TYPE('a::c_type))\<close>.
\<close>
thm root_ptr_valid_def

subsubsection \<open>From byte heap to typed heaps\<close>
text \<open>
In UMM the core wrapper functions to provide a typed view on the raw byte level heap are:
\<^item>\<^term>\<open>h_val::heap_mem \<Rightarrow> 'a::c_type ptr \<Rightarrow> 'a\<close> to lookup typed values by typed pointers and
\<^item>\<^term>\<open>heap_update::'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> heap_mem \<Rightarrow> heap_mem\<close> to update the heap
  on the location designated by a typed pointer with a typed value.

Provided a byte level heap and a heap type description there is a function to lift the
heap into a typed heap:
\<^item>\<^term>\<open>lift_t::'a::c_type ptr_guard \<Rightarrow> heap_mem \<times> heap_typ_desc \<Rightarrow> ('a ptr \<rightharpoonup> 'a)\<close>
 takes a pointer guard and a pair of byte level heap and heap type description and provides a
 partial function from typed pointers to typed values. The most prominent instance
 is abbreviation \<^term>\<open>clift = lift_t c_guard\<close>.

The resulting function is partial as it only lifts those pointers that actually point
to valid addresses according to \<^term>\<open>h_t_valid\<close>. This fact and the connection to \<^const>\<open>h_val\<close>
is reflected in @{thm lift_t_if}.
\<close>
thm lift_t_if

text \<open>To lift root pointers there is
\<^item> \<^term>\<open>simple_lift::heap_mem \<times> heap_typ_desc \<Rightarrow> ('a ptr \<rightharpoonup> 'a::c_type)\<close>.
It yields only defined values for root pointers, according to \<^const>\<open>root_ptr_valid\<close>.
\<close>
thm simple_lift_def

text \<open>
For the derived heaps we introduce the family of functions \<^const>\<open>plift\<close>, which
are defined in @{locale wf_ptr_valid} and instantiated for each collection of open types.
Like \<^term>\<open>clift\<close> the definition is based on \<^const>\<open>lift_t\<close>, but instead of the plain \<^const>\<open>c_guard\<close> a custom
validity-guard for the type is supplied  \<^const>\<open>ptr_valid\<close>. The relevant definitions are collected as named theorems:
\<close>
thm plift_defs

text \<open>
Note that we used to introduced a separate distinct instance of \<^const>\<open>plift\<close> and \<^const>\<open>ptr_valid\<close>
for each type. Now we have encapsulated this construction in @{locale open_types}.
From a specification of which fields of a type should be addressable we first derive an
variant without phantom typing of all the concepts especially \<^const>\<open>open_types.ptr_valid_u\<close> and then
define the phantom typed version based on that. This separation works around the limitation of the
Isabelle type system that are also reflected in locales. It does not allow explicit quantification on type variables.
So we can only have fixed type "variables" in the locale assumptions. However, the lemmas derived within
a locale can still be polymorphic.
So we express the needed assumptions in the locale @{locale open_types} in the "untyped" world and
derive the "typed" polymorphic versions as lemmas within that locale.
\<close>
thm open_struct.ptr_valid_u.simps
thm open_types.ptr_valid_u.simps
thm open_struct.ptr_valid_def
thm open_types.ptr_valid_def



text \<open>
Let us look into the definitions for the open structure \<^typ>\<open>inner_C\<close> which itself is part
of the open structure \<^typ>\<open>outer_C\<close>.
\<close>

lemma "plift h = lift_t (ptr_valid (hrs_htd h)) h"
  by (simp add: open_struct.plift_def)


thm inner_C.ptr_valid.unfold
lemma
  fixes p::"inner_C ptr"
  shows "ptr_valid d p =
    (root_ptr_valid d p \<or>
    (\<exists>q::outer_C ptr. ptr_valid d q \<and> ptr_val p = &(q\<rightarrow>[''inner_C''])) \<or>
    (\<exists>i<5. \<exists>q::(inner_C[5]) ptr. ptr_valid d q \<and> ptr_val p = &(q\<rightarrow>[replicate i CHR ''1''])))"
  by (rule inner_C.ptr_valid.unfold)

lemma
  fixes p::"outer_C ptr"
  shows "ptr_valid d p = root_ptr_valid d p"
  by (simp add: ptr_valid)


text \<open>A pointer to an \<^typ>\<open>inner_C\<close> is valid according to \<^term>\<open>ptr_valid d p\<close>, if it is either
\<^item> a root pointer to an \<^typ>\<open>inner_C\<close>, or
\<^item> there is a valid pointer to an enclosing pointer \<^term>\<open>q::outer_C ptr\<close> to\<^typ>\<open>outer_C\<close>, where
  \<^term>\<open>p::inner_C ptr\<close> is obtained by dereferencing field \<^term>\<open>''inner_C''\<close>, (Note that valid
  \<^typ>\<open>outer_C\<close> are already root pointers). or
\<^item> there is a valid pointer to an array  \<^term>\<open>q::(inner_C[5]) ptr\<close>, where \<^term>\<open>p::inner_C ptr\<close> is obtained
  by indexing into the array. Indexing into arrays is modelled by unary encoded field names
  \<^term>\<open>replicate i CHR ''1''\<close>. (Note that valid array pointers themselve might have 
  various possible extensions to a root pointer of an enclosing structure)

These pointer-valid predicates are derived from the specification of addressable fields in the
corresponding @{command autocorres} command. They enumerate the possibilities to arrive
at a valid pointer starting from a valid root-pointer. The specification is converted to
the parameter \<^const>\<open>\<T>\<close> of \<^locale>\<open>open_types\<close>. In our example program this is:
\<close>


thm \<T>_def

text \<open>The \<^const>\<open>\<T>\<close> is an association list mapping a type tag \<^const>\<open>typ_uinfo_t\<close>
of a \<^class>\<open>mem_type\<close> to the list of addressable fields within that structure. From this
specification we derive a lot of useful notions within the locale. Notably:
\<close>
thm ptr_valid         \<comment> \<open>These go up the chain to the root pointer.\<close>

subsubsection \<open>From typed heaps to split heaps\<close>

text \<open>
Note that the functions in the previous subsubsection still are defined on the level of the
monolithic UMM memory model. They are central building blocks to finally arrive at the split
heap model.
Essentially there is a split heap component in the lifted globals corresponding
to \<^const>\<open>plift\<close> for all the fundamental types.

However, instead of partial functions as provided by \<^const>\<open>wf_ptr_valid.plift\<close>
the split heap separates definedness from the actual value, by providing a pair of a total function
from pointer to value and a validity predicate which indicates definedness. This design choice
was introduced in the original AutoCorres.

As a prerequisite to lift the Functions into the split heap model, the new global state record
@{typ lifted_globals} is defined. For each fundamental heap this record contains a field for
 the split heap e.g.
\<^term>\<open>heap_w32::lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> 32 word\<close>.

These are the lookup functions provided by the record package, there are of course also
the corresponding update functions, e.g.:
 \<^term>\<open>heap_w32_update::  ((32 word ptr \<Rightarrow> 32 word) \<Rightarrow> (32 word ptr \<Rightarrow> 32 word)) \<Rightarrow>
        lifted_globals \<Rightarrow> lifted_globals\<close>
Note that the update function behaves like a "map", which maps an update function on the selected
heap to an update function on \<^typ>\<open>lifted_globals\<close>.

The typing information (heap type description) is preserved from the monolithic heap in component
\<^term>\<open>heap_typing :: lifted_globals \<Rightarrow> heap_typ_desc\<close>.

\<close>
print_record lifted_globals

text \<open>For the derived heaps we provide a similar abstraction level by defining a derived heap lookup and
a derived heap update function. These functions are a composition of
the underlying functions for the fields of the structure.
\<close>
thm derived_heap_defs

text \<open>For example for \<^typ>\<open>outer_C\<close> we have.

\<^item> Lookup:  \<^term>\<open>heap_outer_C:: lifted_globals \<Rightarrow> outer_C ptr \<Rightarrow> outer_C\<close>
\<^item> Pointwise update: \<^term>\<open>heap_outer_C_map:: outer_C ptr \<Rightarrow> (outer_C \<Rightarrow> outer_C) \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals\<close>
\<^item> Validity is generically based on the heap typing for all heaps:
   \<^term>\<open>(\<lambda>s. ptr_valid (heap_typing s)):: lifted_globals \<Rightarrow> 'a::mem_type ptr \<Rightarrow> bool\<close>

Note the difference in the signature of the derived update \<^const>\<open>heap_outer_C_map\<close> and
the fundamental \<^const>\<open>heap_w32_update\<close>. Besides the difference in naming between 'map' and
'update', the derived update is defined pointwise instead of heap-wide. The reason is
that the pointwise update is what we actually need for autocorres and it is natural to
break down a pointwise update defined via a function on
\<^term>\<open>f:: outer_C \<Rightarrow> outer_C\<close> to the update functions on the fields of \<^typ>\<open>outer_C\<close>.
\<close>
thm heap_outer_C_def
thm heap_outer_C_map_def


text \<open>
The connection between \<^typ>\<open>globals\<close> (containing the byte level heap) and \<^typ>\<open>lifted_globals\<close>
is defined via the function \<^term>\<open>lift_global_heap::globals => lifted_globals\<close>.
The fundamental heaps are lifted via the corresponding \<^const>\<open>wf_ptr_valid.plift\<close>
functions. Validity of pointers is maintained by literally preserving the heap typing from the
monolithic heap.
\<close>
thm "lift_global_heap_def"
thm "lift_t_def"
thm plift_defs

text \<open>\<close>
subsection \<open>User Level \<close>

text \<open>
Due to the abstraction layer of derived heap types, the structure of the programs after
heap lifting is analogous for closed and opened structures.
\<close>
context ts_definition_set_c1
begin
thm ts_def

lemma "set_c1' p c \<equiv> do {guard (\<lambda>s. IS_VALID(closed_C) s p);
                    modify (heap_closed_C_update (\<lambda>h. h(p := c1_C_update (\<lambda>_. c) (h p))))
                 }"
  by (rule ts_def)

end

context ts_definition_outer_fld1_upd
begin
thm ts_def
end

context ts_definition_set_element
begin
thm ts_def
end

context ts_definition_set_matrix_element
begin
thm ts_def
end

text \<open>Of course, when it comes to specifications and proving properties about the programs,
the user has to take care about aliasing of addressable fields.
AutoCorres generates a bunch of theorems and sets up the simpsets with some obvious rules for
derived heaps, which hopefully helps in doing so. However, as a last resort one might still have
to unfold the definitions and work with the parts.
Here is some examples of some theorems or collections of theorems.
\<close>
thm lifted_globals_ext_simps
thm ptr_valid

thm heap_inner_C.write_comp
thm heap_inner_C.write_id
thm heap_inner_C.write_other_commute
thm heap_inner_C.write_same
thm update_commute
thm read_write_same
thm read_write_other
thm write_cong
thm update_compose
thm valid_implies_c_guard
thm read_commutes
thm write_commutes

thm fg_cons_simps
thm typ_info_simps
thm td_names_simps
thm typ_name_simps
thm upd_lift_simps (* TODO: REMOVE EMPTY *)
thm upd_other_simps  (* TODO: REMOVE EMPTY *)
thm size_align_simps
thm fl_Some_simps
thm fl_ti_simps
thm typ_tag_defs
thm size_simps
thm typ_name_itself

subsubsection \<open>\<^term>\<open>addressable_fields\<close>,\<^term>\<open>merge_addressable_fields\<close>,\<^term>\<open>read_dedicated_heap\<close>,\<^term>\<open>write_dedicated_heap\<close>\<close>

text \<open>
We distinguish three aspects when thinking and reasoning about split heaps: the
monolithic heap stored in \<^typ>\<open>globals\<close> the split heap components in \<^typ>\<open>lifted_globals\<close> and
the function \<^const>\<open>lift_global_heap\<close> which transforms between both types. Autocorres does a 
refinement proof that a program operating on \<^typ>\<open>lifted_globals\<close> refines a program 
on \<^typ>\<open>globals\<close> where the heaps are related by function \<^const>\<open>lift_global_heap\<close>.

For open structures, the fields which are addressable have two representations in \<^type>\<open>lifted_globals\<close>:
\<^enum> the relevant value in the common heap, i.e. \<^const>\<open>heap_w32\<close> for the \<open>inner.fld1\<close> pointers
\<^enum> an unused value in the field of the dedicate heap, i.e. the \<open>fld1_C\<close> in the \<^const>\<open>dedicated_heap_inner_C\<close>.
Having the dedicated heap allows us to keep all non-addressable fields of a structure in a single split
heap component of \<^typ>\<open>lifted_globals\<close>. The values of the addressable fields are irrelevant for
the virtual heap. When reading from a virtual heap we start with the value in the dedicated heap and
overwrite the addressable fields by considering the common heaps.
\<close>

thm "heap_inner_C_def"

text \<open>When writing to a virtual heap we have a series of updates on \<^typ>\<open>lifted_globals\<close>. We start by 
updating the non-addressable fields in the dedicated heap and then updating the common heaps with the
new values for the addressable fields:\<close>

thm "heap_inner_C_map_def"

text \<open>To express "update the non-addressable fields of the dedicated heap" in an uniform way
we make use of the concept of \<^emph>\<open>scenes\<close> from the world of \<^emph>\<open>lenses\<close>. In contrast to lenses, 
scenes are formalised by properties of a single function \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> which is referred to as
˜\<^emph>\<open>merge\<close> or 'overrider' operation. The intuition of \<^term>\<open>merge x y\<close> is that we take certain
portions of a compound value \<^term>\<open>x\<close> and merge (or override) them into another compound value
 \<^term>\<open>y\<close>. Scenes are formalised in locale \<^locale>\<open>is_scene\<close>. The notion \<^emph>\<open>merge\<close> emphasises the
the symmetric nature of the merge operation. Like a lense, a scene 'focuses' on a portion of a 
compound value \<^typ>\<open>'a\<close>. The merge operation takes that portion from the first argument and the 
complement of that portion from the second argument. Think for example of a pair and the 'portion' being
the first component. Then @{term "merge x y = (fst x, snd y)"}. The notion \<^emph>\<open>overrider\<close> puts more 
emphasis on the merge as an update function, in particular this view becomes obvious if we think
of a partial application @{term "merge x"}: this is an update function which overrides the 'portion'
within an value @{term y} to that portion of @{term x}. You can also think of fixing the 'portion' to
those values in @{term x}. Analogously @{term "\<lambda>x. merge x y"} fixes the complement of the 'portion' to
those values in @{term y}.
Scenes are closely related to lenses in the sense that it is straightforward to derive a 
scene from a lense @{thm is_scene_of_lense}.
\<close>

thm is_scene_of_lense

text \<open>For HOL the decisive advantage of scenes compared to lenses is that they only have one type parameter,
which fixes the type of the compound value. But still you can formally 'talk' about different 'portions' of
that value in an uniform way. For example you can have a list or a set of scenes to describe their
composition. This property can be used to uniformly describe "all addressable fields" of a value or 
"all non-addressable fields" of a value. 

The relevant merging function for us is \<^term>\<open>merge_addressable_fields\<close> which is an 
abbreviation \<^term>\<open>open_types.merge_addressable_fields\<close>.
\<close>

term \<open>open_types.merge_addressable_fields\<close>

text \<open>
The term\<^term>\<open>merge_addressable_fields old new\<close> has to effects:
\<^item> The addressable fields are taken from \<^term>\<open>old\<close>
\<^item> The non-addressable fields are taken from \<^term>\<open>new\<close>.
\<close>

text \<open>To express the same semantics that we have just described for \<^typ>\<open>lifted_globals\<close> on the 
UMM heap in \<^typ>\<open>globals\<close> we make use of the functions \<^const>\<open>read_dedicated_heap\<close> and
 \<^const>\<open>write_dedicated_heap\<close>. These functions internally again make use of \<^term>\<open>merge_addressable_fields\<close>.
We zero out all parts of the compound value we are not actually interested in. This gives us
canonical values which we can easily relate to the \<^typ>\<open>lifted_globals\<close>. For example
for \<^term>\<open>read_dedicated_heap\<close> we zero out all addressable fields and also all values which
are not even \<^term>\<open>ptr_valid\<close> (according to \<^const>\<open>plift\<close>).
\<close>

lemma (in open_types) 
  "read_dedicated_heap h p = 
     merge_addressable_fields ZERO('a::mem_type) (the_default ZERO('a) (plift h p))"
  by (simp add: read_dedicated_heap_def)

thm open_types.read_dedicated_heap_def
thm open_types.write_dedicated_heap_def

text \<open>The lifting function \<^const>\<open>lift_global_heap\<close> directly uses \<^const>\<open>read_dedicated_heap\<close> to 
construct a dedicated heap from the UMM heap:\<close>
thm lift_global_heap_def


text \<open>
To have a canonical representation we overwrite the fields in the dedicated heap with zeros, using the
generic constants \<^const>\<open>addressable_fields\<close> and \<^const>\<open>merge_addressable_fields\<close> defined in 
\<^locale>\<open>open_types\<close>.

\<^term>\<open>read_dedicated_heap\<close>,\<^term>\<open>write_dedicated_heap\<close> combine these with \<^term>\<open>h_val\<close>, to get the
canonical heap access.

\<close>




subsubsection \<open>Why all the variants? \<^term>\<open>h_val\<close> / \<^term>\<open>read_dedicated_heap\<close> \<close>


thm lifted_globals_ext_simps
thm lift_global_heap_def
thm open_types.read_dedicated_heap_def
text \<open>
When taking a close look in the definition of \<^const>\<open>lift_global_heap\<close> one sees that the
abstraction for a split heap component from the monolithic heap is:

\<^term>\<open>read_dedicated_heap (t_hrs_' g)\<close>

So this might seem a bit surprising at first sight. What is all the indirection useful for:
\<^enum> the \<^const>\<open>read_dedicated_heap\<close> adds an option layer to the plain \<^const>\<open>h_val\<close> and \<^const>\<open>plift\<close>
\<^enum> with \<^term>\<open>t_hrs_'\<close> we get the heap representation (including bytes and types)

When we know that a pointer is valid there is a tight connection between \<^const>\<open>read_dedicated_heap\<close> and \<^const>\<open>h_val\<close>
\<close>
thm open_struct.ptr_valid.ptr_valid_plift_Some_hval
thm open_struct.read_dedicated_heap_def

text \<open>
This connection directly carries over to lifting.
\<close>
thm read_commutes

text \<open>
The difference between \<^const>\<open>read_dedicated_heap\<close> and \<^const>\<open>h_val\<close> becomes apparent when looking at partial heaps and invalid
pointers. While \<^const>\<open>read_dedicated_heap\<close> always yields \<^const>\<open>c_type_class.zero\<close> the plain \<^const>\<open>h_val\<close> will still construct
some value out of the bytes in the heap. So in a sense the indirection to \<^const>\<open>read_dedicated_heap\<close> makes
heaps equal if the agree on the valid pointers only. So we encode "heap equality only on valid pointers" in
an ordinary equality on the complete lifted heap. This choice ensure compositionality for
the polymorphic \<^const>\<open>c_type_class.zero\<close>, in the sense that the \<^const>\<open>c_type_class.zero\<close> of a structure means that all subcomponents
are \<^const>\<open>c_type_class.zero\<close>.

Moreover \<^const>\<open>read_dedicated_heap\<close> only reads the fields which are not addressable, and overwrites the
addressable fields with \<^const>\<open>c_type_class.zero\<close>. This gives us a canonical view on the partial heap.
\<close>

thm zero_simps
thm open_struct.ptr_valid.plift_None

(* FIXME *)
subsubsection \<open>I miss the typing in the split heap!\<close>

text \<open>
A peculiar property of the original split heap model of autocorres was that you loose parts of
the type information that were directly available in the byte-level heap. There was no
heap-type description in \<^typ>\<open>lifted_globals\<close> but only the more abstract \<open>is_valid_<type>\<close> fields for
each type. For closed types this isn't so much of an issue as
essentially all relevant type information is captured in the fact that all pointers to that
type have a distinct split heap, which is separate from all other split heaps.
But for shared types this is no longer true. Thus we maintain the typing information also
in the split heap in the compponent \<^const>\<open>heap_typing\<close>. The relation to the typing information of
the original byte-level heap is encapsulated in \<^const>\<open>lift_global_heap\<close>. For low-level
operations that are embedded via \<^const>\<open>exec_concrete\<close> you can directly connect the typing of the
monolithic and the split heap. In particular you can derive
\<^term>\<open>c_guard p\<close> from that information. Or you can derive that if you have two valid pointers
of the same type, where you only know that the address is different, you can still conclude that
the complete pointer span of the pointers do not overlap.

But keep in mind that typing is only a "discipline". As in the split heap you can manipulate the
values on the heap or split heap independent of the typing information. When well-typedness or
\<^const>\<open>ptr_valid\<close> is available you might be able to derive properties like distinctness of pointer
spans. The distinctness of pointers spans is the actual reason that certain heap updates commute,
e.g. @{thm heap_inner_C.write_other_commute}
\<close>
thm heap_inner_C.write_other_commute



subsection \<open>Simulation Proof\<close>

text \<open>
The simulation of a concrete program \<^term>\<open>C::('a, 'b, globals) exn_monad\<close> operating
on the byte-level heap by an
abstract program \<^term>\<open>A::('a, 'b, lifted_globals) exn_monad\<close> operating on the split heaps
is captured in predicate\<^term>\<open>L2Tcorres lift_global_heap A C\<close>. The proof for an instance
of \<^term>\<open>C\<close> follows the syntactic structure of \<^term>\<open>C\<close> by applying introduction rules and
synthesizing the abstract program \<^term>\<open>A\<close>.

Intuitively the core properties on which the simulation proof builds are:
\<^item> Abstract programs only operate on abstract heap values not on byte-lists. Byte-level concepts
  like padding fields are irrelevant for the abstract program. The abstract heaps and
  programs don't distinguish between two byte-level heaps if they agree on all values
  of non-padding fields of properly allocated and typed portions of the heap.
\<^item> Lookup and update via a pointer into a structure can be simulated by an lookup and update
  via the root pointer of the structure.
\<^item> Each non-addressable field of a structure is mapped into exactly one split heap. For a 'closed' structure
  without any addressable fields this is the heap for the type.
\<^item> For an 'open' structure an addressable field is mapped into a shared heap or multiple shared
  heaps in case the field is again an open structure.
\<^item> The pointer spans of two valid root pointers of different types do not overlap.
\<^item> The pointer spans of two valid root pointers to the same type might overlap only if the pointer value is
  the same.

The actual proof of a simulation is divided into three main steps.
\<^item> First some general theorems relating byte-level and split heaps are derived. Most prominently
  \<^const>\<open>typ_heap_simulation\<close> and related predicates.
\<^item> These theorems are used to instantiate the syntax driven introduction rules collected in
  named theorems @{thm heap_abs}.
\<^item> The derived introduction rules are recursively applied to the program.

The first step is the one that was significantly extended to support addressable
fields in open structures. The second and third step remained almost unchanged.
\<close>
thm heap_abs
text \<open>
When thoroughly inspecting the rules @{thm heap_abs} and keeping in mind that they are
used by recursively applying them as introduction rules to a concrete program \<^term>\<open>C\<close> and a
schematic variable for the abstract program \<^term>\<open>A\<close> one can see the following strategy:
\<^item> First some normalisation of expressions involving pointers is performed on the concrete
  program \<^term>\<open>C\<close>. In particular an update to a dereferenced pointer \<^term>\<open>&(p\<rightarrow>f)\<close> by a value \<^term>\<open>v\<close>
  is transformed to an update on \<^term>\<open>p\<close>, where first the value of \<^term>\<open>p\<close> is fetched from memory and
  then field \<^term>\<open>f\<close> of this value is updated by \<^term>\<open>v\<close> and the resulting compound value is put
  back to memory.
\<^item> Only after the normalisation on \<^term>\<open>C\<close>, the actual translation to an abstract \<^term>\<open>A\<close> on the
  split heap is performed.

The normalisation step is guided by predicates \<^const>\<open>struct_rewrite_guard\<close>,
 \<^const>\<open>struct_rewrite_expr\<close> and  \<^const>\<open>struct_rewrite_modifies\<close>.
After that normalisation the atomic building block for the simulation is provided by an
instance of \<^const>\<open>typ_heap_simulation\<close>, which tells how a lookup and update of a pointer of a
given type in the byte heap is simulated in the split heap.

The proofs of the necessary instances of \<^const>\<open>typ_heap_simulation\<close> are provided once and forall in
the initialisation phase of @{command autocorres} or @{command "init-autocorres"}. They are provided
for atomic and shared heaps as well as derived heaps.
\<close>

subsubsection \<open>Proving \<^const>\<open>typ_heap_simulation\<close>\<close>

text \<open>As stated before this step was extended quite excessively and quite some infrastructure
of both theorems as well as ML code were built to support it.

\<close>

paragraph \<open>Typed vs. Untyped Dialects/ Records vs. Byte-Lists\<close>

text \<open>
First some general remarks on the general concepts and setup. The UMM was designed in the
spirit to take advantage of HOL type and class inference to support reasoning about C-types and
pointers. As a consequence some of the definitions and theorems are rather subtle and somehow
live an the edge of what can be typed and expressed in the HOL type system. Sometimes the
essence or the limitations of a theorem only become 'visible' when also looking at the
types of expressions, especially the pointer types. Unfortunately writing about these
concepts is rather ambiguous with respect to the notion type. 'Type' might refer to
the original C-structure in the C program, this type is related to an abstract HOL-type, which
is a record. This record is an instance of various type-classes: \<^class>\<open>c_type\<close>, \<^class>\<open>mem_type\<close>,
 \<^class>\<open>xmem_type\<close>. For types of \<^class>\<open>c_type\<close> we define overloaded \<^const>\<open>typ_info_t\<close>, which
associates a HOL-term describing the type (referred to as type-description or type-information). Moreover,
pointers represented in HOL carry the HOL-type they point to as phantom type.

An illustration for the subtle typing is the two terms
 \<^term>\<open>&(p\<rightarrow>f) \<noteq> &(q\<rightarrow>g)\<close> vs. \<^term>\<open>p \<noteq> q \<Longrightarrow> &(p\<rightarrow>f) \<noteq> &(q\<rightarrow>g)\<close>.
Whereas in first term the pointers \<^term>\<open>p::'a ptr\<close> and \<^term>\<open>q::'b ptr\<close> have a different type, in the second
term they both have the same type as the inequation in the precondition also makes the types equal.
This might not always be the intended meaning. When the type of the pointer is
irrelevant one might resort to plain addresses instead of pointers \<^term>\<open>ptr_val p = ptr_val q \<Longrightarrow> &(p\<rightarrow>f) = &(q\<rightarrow>g)\<close>.
This general theme occurs in various places. There often is a typed variant of a concept
and also an untyped variant, based on addresses or byte lists, like \<^term>\<open>p\<close> vs. \<^term>\<open>ptr_val p\<close>.
Both are closely related. The typed variant somehow reflects the 'API' of the concept and
is more abstract, whereas during a proof one actually resort to the untyped variant
to gain flexibility. These two views on a concepts leads to a duplication of lemmas.
Moreover, a lemma might not immediately be available in the form one expects, but can
be 'easily' derived from some related lemmas.


The central UMM HOL-datatype to reflect C-types into HOL terms is \<^typ>\<open>('a, 'b) typ_desc\<close> and is defined
mutually recursive with \<^typ>\<open>('a, 'b) typ_struct\<close>. It is basically a tree describing the
nested structure of an aggregate type. Field names, alignment and size information is encoded,
and lookup and update of sub-fields can be derived from this information.


The most prominent instances of this type are the typed variant\<^typ>\<open>'a xtyp_info\<close> vs. the
 untyped variant \<^typ>\<open>typ_uinfo\<close>. The former can be transformed to the latter by
 \<^const>\<open>export_uinfo\<close>. As with pointer types the type variable in \<^typ>\<open>'a xtyp_info\<close> denotes
the abstract  HOL-C-type that is described by the type information. So to derive a field-lookup or
field-update on HOL-types from the type information one needs to resort to the typed variant.
Exporting the type information via \<^const>\<open>export_uinfo\<close> maintains the shape of the tree, but
removes all the HOL-C-type dependent components. The resulting \<^typ>\<open>typ_uinfo\<close> has two main
use cases:
\<^item> It can be seen as a type-tag identifying a C-type. It can be used to relate two C-types on
  the HOL-term level, e.g. ask if they are equal or if one is contained in the other.
\<^item> It can be used to normalise a byte-list representing a value of that type. Normalisation means
  that all padding bytes in the byte-list are set to zero.

For each C-type the C-Parser also generates the type information which can be
accessed via the overloaded function: \<^term>\<open>typ_info_t TYPE('a::c_type)\<close>.

The main use cases for \<^term>\<open>typ_info_t TYPE('a::c_type)\<close> are
\<^item> Provide lenses for fields (access / update) on the abstract value (record),
  via \<^const>\<open>access_ti\<close>, \<^const>\<open>update_ti\<close> and \<^const>\<open>field_lookup\<close>
The main use cases for \<^term>\<open>typ_uinfo_t TYPE('a::c_type)\<close> are
\<^item> comparison of type descriptors: equality and order \<^term>\<open>s \<le>\<^sub>\<tau> t\<close>
\<^item> normalisation of byte-lists \<^const>\<open>norm_tu\<close>, in particular setting all padding bytes to zero.
\<close>
thm sub_typ_def
thm typ_tag_le_def
text\<open>
So \<^const>\<open>typ_info_t\<close> is more related to the abstract view on a value (as a HOL record), whereas
\<^const>\<open>typ_uinfo_t\<close> is more related to the byte-list encoding of the value.
This duality somehow also reflects the dual nature of types in C. On the one hand C is a
statically typed language and on the other hand it allows to break the abstraction and switch to
a low-level byte oriented view.
\<close>

context
  fixes p::"'a::c_type ptr"
  fixes f::"qualified_field_name"
  fixes t::"'a xtyp_info"
  fixes n:: nat
begin
text \<open>
A central function on both typed and untyped typ-information is the
function \<^const>\<open>field_lookup\<close> which retrieves the type-information for a field of a type.
A common application of this function is to state some property on a dereferenced pointer:
\<^term>\<open>PTR('b) &(p\<rightarrow>f)\<close>. Note that \<^term>\<open>p\<close> is an pointer to an \<^typ>\<open>'a\<close>: \<^term>\<open>p::'a ptr\<close>.
A typical precondition is to retrieve the type-information for field \<^term>\<open>f\<close> from the
type information of \<^typ>\<open>'a\<close>:
 \<^term>\<open>field_lookup (typ_info_t TYPE('a)) f 0 = Some (t::'a xtyp_info, n)\<close>

Note that the retrieved type information \<^term>\<open>t::'a xtyp_info\<close> is still tagged with
\<^typ>\<open>'a\<close>. The number \<^term>\<open>n\<close> is the offset of the selected field.
Typically we want to relate \<^term>\<open>t\<close> to the type of the selected field \<^typ>\<open>'b\<close> (which
only happens to be the same \<^typ>\<open>'a\<close> in case the field is the empty list).
The relation can be established via \<^term>\<open>export_uinfo\<close>, namely
 \<^term>\<open>export_uinfo t = export_uinfo (typ_info_t TYPE('b::c_type))\<close>.
Note that directly equating \<^term>\<open>t\<close> to \<^term>\<open>typ_info_t TYPE('b::c_type)\<close> is not even
a well-typed expression in HOL, as \<^typ>\<open>'a\<close> is not equal to \<^typ>\<open>'b\<close>.

The right hand side abbreviates to constant \<^term>\<open>typ_uinfo_t TYPE('b::c_type)\<close>.
\<close>
end

text \<open>A concrete example might give some further insight to the relation of \<^const>\<open>typ_info_t\<close> and
\<^const>\<open>typ_uinfo_t\<close> and how the type-information is constructed. Let us consider the field
 \<^term>\<open>''inner_C''\<close> of \<^typ>\<open>outer_C\<close>, which selects a field of \<^typ>\<open>inner_C\<close>.
We can retrieve the information for the field:\<close>

lemma "field_lookup (typ_info_t TYPE(outer_C)) [''inner_C''] 0 =
  Some (adjust_ti (typ_info_t TYPE(inner_C)) outer_C.inner_C (inner_C_update \<circ> (\<lambda>x _. x)), 0)"
  by (simp)

text \<open>
Note that the retrieved type information is constructed from the nested type information
for \<^typ>\<open>inner_C\<close>, by adjusting it. Adjusting means that we say how we can lookup and update
the sub-field of the record \<^typ>\<open>outer_C\<close>. This adjustment only affects the typed-view of
the type information. Exporting the type information collapses to the adjusted inner type:
\<close>

lemma "export_uinfo (adjust_ti (typ_info_t TYPE(inner_C)) outer_C.inner_C (inner_C_update \<circ> (\<lambda>x _. x)))
     = export_uinfo (typ_info_t TYPE(inner_C))"
  by simp

text \<open>
In the realm of 'lenses", \<^const>\<open>adjust_ti\<close> can be viewed as a form of composition of lenses.
A lense for an inner type is transformed to a lense on the outer type.
The lense assotiated to type information is captured in \<^const>\<open>access_ti\<close>, for the 'lense-lookup'
aka. 'lense-get' part, and \<^const>\<open>update_ti\<close> for the 'lense-update' aka 'lense-put'.

Function \<^term>\<open>field_lookup\<close> is the essential building block to relate field names e.g. as
part of dereferencing a pointer to their abstracts operations on the associated HOL-type.
One can convert between the typed and untyped version:
\<close>
thm "field_lookup_export_uinfo_Some_rev"
thm "field_lookup_export_uinfo_Some"

text  \<open>
Here are some closely related, mostly derived concepts around \<^term>\<open>field_lookup\<close>:
\<^item> \<^const>\<open>field_lookup\<close>, \<^const>\<open>field_ti\<close>, \<^const>\<open>field_offset\<close>, \<^const>\<open>field_of\<close>
\<^item> \<^const>\<open>td_set\<close>, \<^const>\<open>sub_typ\<close> (\<^term>\<open> s \<le>\<^sub>\<tau> t\<close>
\<^item> Family of field name functions: \<^const>\<open>all_field_names\<close>, \<^const>\<open>field_names\<close>, \<^const>\<open>field_names_u\<close>,
  \<^const>\<open>field_names_no_padding\<close>,  \<^const>\<open>all_field_names_no_padding\<close>

Often lemmas might not be available for all variants, but via some simple indirections, via
definitions or conversion lemmas. In an Isar-proof, @{command sledgehammer} can often help to
find the connections.
\<close>
thm td_set_field_lookupD
thm td_set_field_lookup
thm all_field_names_union_field_names_export_uinfo_conv
thm set_field_names_all_field_names_conv
thm field_names_u_field_names_export_uinfo_conv(1)
thm set_field_names_no_padding_all_field_names_no_padding_conv
thm all_field_names_no_padding_typ_uinfo_t_conv

paragraph \<open>Doing the Proof\<close>

text \<open>
The fundamental goal is to derive interpretations @{locale typ_heap_simulation} for every relevant
type. It states that the virtual heap for a type as obtained from @{typ lifted_globals} simulates the
original UMM heap in @{typ globals}. Both states are connected by the abstraction 
function @{const lift_global_heap} which is the abstract function @{term st} in @{locale typ_heap_simulation}.
To facilitate the construction of the proofs we introduce intermediate helper locale 
@{locale typ_heap_simulation_open_types} and 
make use of the infrastructure of lenses and scenes that we mentioned before.

To optimize the construction (in particular to minimise the number of heaps we have to put into into
@{typ lifted_globals}) we distinguish three main cases:
\<^item> A structure is closed and has no addressable fields: @{thm open_types.typ_heap_simulationI_no_addressable}
  In this case there is only one relevant heap in @{typ lifted_globals}. 
  No overlay of a dedicated heap with some common heaps is necessary.
\<^item> A structure is completely open, meaning that all fields are addressable: @{thm open_types.typ_heap_simulationI_all_addressable}.
  In this case we do not need a dedicated heap. The structure is described by a overlay of 
  common heaps.
\<^item> A structure is partially open, some fields are addressable and some not: @{thm open_types.typ_heap_simulationI_part_addressable}.
  In that case we need an overlay of a dedicated heap and some common heaps.

On an intuitive abstract level the lemmas and proof argue about composing field-level lookup and updates
within some heap(s) to lookup and updates of the complete compound structure. We want to argue that lookup and
update in the UMM heap is simulated by the overlayed updates of a dedicated heap and some common
heaps in the split heap. To argue about different fields of a structure we build on the idea of scenes
and also extend it to reads. Note that the general problem is that a structure is represented as
a HOL record and each field has a distinct type. Because of the limitations of the HOL type system
we cannot directly combine e.g. functions like readers for different fields like \<^typ>\<open>'a \<Rightarrow> 'b1\<close> 
and \<^typ>\<open>'a \<Rightarrow> 'b2\<close> in a HOL list. Here the scene idea to express everything via a merge or update
on \<^typ>\<open>'a\<close> is a helpful 'trick'. E.g. 'reading' the value of a field can in a sense be as well 
expressed as a function \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> that reads the field of the first argument and puts it into any
structure you give it as second argument:
\<close>

thm lift_global_heap_def
thm open_types.typ_heap_simulationI_all_addressable
thm open_types.typ_heap_simulationI_part_addressable
thm open_types.typ_heap_simulationI_no_addressable
thm pointer_lense_def
thm partial_pointer_lense_def
thm typ_heap_simulation_of_field_def
text \<open>
Other important building blocks are:
\<^item> @{locale pointer_lense} which describes a virtual heap.
\<^item> @{locale partial_pointer_lense} which describes the effect of field lookup / updates on a virtual heap by
 combining a scene identifying the field and the pointer lense for the virtual heap.
\<^item> @{thm typ_heap_simulation_of_field_def} which is used to break down @{locale typ_heap_simulation} to the 
level of fields in the structure.
\<close>

text \<open>
The automation is implemented in @{ML \<open>HeapLiftBase.gen_new_heap\<close>}.

The following paragraphs describe some abstract arguments and lemma collections. In a previous
version the proof @{locale typ_heap_simulation} was more directly based on those arguments 
implemented in ML. Meanwhile we were able to replace most parts of the ML code by lemmas 
described before based on scenes and pointer lenses. Nevertheless the arguments are still valid
and the lemma collections might be useful in other places.
\<close>

paragraph \<open>Fundamental heaps\<close>
text \<open>
We start with the fundamental heaps.
The simulation property for heap-updates is captured in @{locale write_simulation}. It
is a commutation property. Provided we have a valid pointer in the split heap (obtained from
lifting from the byte-level heap), we can
either first perform the heap update in the byte-level heap and then lift the
state via \<^const>\<open>lift_global_heap\<close>, or first lift the byte-level heap into the split heap and
apply the corresponding update there. Both ways yield the same final state.
So we have to prove equality of two states of \<^typ>\<open>lifted_globals\<close>. The first question is
which parts of the state did change? Intuitively only the affected split heap did change,
all other heaps stayed the same. But all split heaps are derived from the same byte level heap.
So the proof decomposes into two main arguments, one is for
the affected heap where we have to show that both updates, the one on the byte-level heap and and the one on the
affected split heap, are the same. The other argument is that all other split heaps remain unchanged.
Actually the first case is the more straight forward one and could be handled with theorems like
 @{thm plift_heap_update}.
\<close>
thm plift_heap_update

text \<open>
 The second case, to prove what
is not changed is more involved. As a split heap might not only contain root pointers but
also valid pointers that are nested in other types we have to distinguish several cases.
We developed a general theory in \<^locale>\<open>open_types\<close> and the essential theorems for the commutation
proof are collected in @{thm plift_simps}.
When we update the heap at pointer \<^term>\<open>p::'a ptr\<close> and lookup the value of pointer \<^term>\<open>q::'b ptr\<close>
we can distinguish various cases by analysing the type relation (e.g. if one type is nested in the
other). Note that by introducing guards into the code and the design of \<^term>\<open>lift_global_heap\<close>
we only have to care about the case were both pointers are valid according to \<^const>\<open>ptr_valid\<close>.
To be more specific. That the pointer that is updated is \<^term>\<open>ptr_valid\<close> is ensured by the
corresponding guard on the update. That the pointer we read from is actually \<^term>\<open>ptr_valid\<close> is more
subtle. Here we rely on the construction of \<^const>\<open>lift_global_heap\<close> were a split heap is
constructed by \<^term>\<open> \<lambda>p. the_default c_type_class.zero (plift (t_hrs_' g) p)\<close>. In case the pointer is
invalid we always obtain \<^term>\<open>c_type_class.zero\<close> and hence only the valid pointers may be affected by an heap update.
This reduction to valid pointers and \<^term>\<open>h_val\<close> is encapsulated in theorems @{thm plift_eqI}.
\<close>

thm lift_global_heap_def
thm the_plift_hval_eqI
thm plift_eqI
thm plift_simps

paragraph \<open>Treatment of Array Types\<close>

text \<open>
At the core there is no special type-information for array types. It is treated analogously
to structures. Each index gets an individual field name which is the unary encoding of the index.
The good thing is that one does not need any new fundamental lemmas to deal with array types.
But it is not a good idea to unfold the type-information for arrays and to work on that
expanded version. On the one hand things like simplification might become slow, on the other
hand we can make use of the regular structure of array types and once and forall derive
general lemmas.

The central theorems to work with field-lookup in arrays are @{thm field_lookup_array}
and @{thm array_ptr_index_field_lvalue_conv}. The latter one allows to convert between
an array-index-arithmetic based view of array pointers \<^term>\<open>array_ptr_index p False i\<close>
and the field-name view \<^term>\<open>Ptr &(p\<rightarrow>[replicate i CHR ''1''])\<close>.
\<close>
thm field_lookup_array
thm array_ptr_index_field_lvalue_conv
text \<open>
These theorems are used to normalise array accesses towards symbolic field name
accesses of the format term>\<open>Ptr &(p\<rightarrow>[replicate i CHR ''1''])\<close>. Note that we don't unfold
the definition of \<^const>\<open>replicate\<close> here, and index \<^term>\<open>i\<close> stays abstract, constrained
by precondition that limits its range.
\<close>
thm unpacked_C.ptr_valid.unfold
thm unpacked_C'array_2.ptr_valid.unfold

text \<open>
The instances of @{locale typ_heap_simulation} can be established from  @{locale typ_heap_simulation}
of the element types. We introduce the locales @{locale array_typ_heap_simulation} and
@{locale two_dimensional_array_typ_heap_simulation} to automatically provide the sublocale relations when the
element type falls into \<^class>\<open>array_outer_max_size\<close> or \<^class>\<open>array_inner_max_size\<close>
respectively.
\<close>

paragraph \<open>Derived Heaps\<close>

text \<open>
The commutation proofs for derived heaps follow another path. For derived heaps we can assume
that we have all the instances of @{locale typ_heap_simulation} of the component types already
available. 
Unaddressable fields are never shared. Pointers only appear within a dedicated enclosing parent structure.
Validity of the pointer coincides with validity of the parent pointer. Pointers that are mapped by the
field heap coincide with the parent pointers, there is no need to calculate the offset of the field.
So deriving the commutation proof from the available theorems boils down to their composition.
The central lemma connects an update of a derived heap to an fold over the updates of the
toplevel fields: @{thm heap_update_fold_toplevel_fields_pointless}.
Moreover, we establish that @{const heap_update_padding} is equivalent to @{const heap_update} under
the state lifting function. Padding bytes become irrelevant in the split heap.
For each toplevel field we have the
commutation proof connecting the monolithic byte-level
heap update to the split-heap update collected in @{thm write_commutes}.
\<close>
thm heap_update_fold_toplevel_fields_pointless
thm plift_heap_update_padding_heap_update_pointless_conv
thm lift_heap_update_padding_heap_update_conv
thm write_commutes


subsubsection "No restriction to \<^class>\<open>packed_type\<close>!"

text \<open>
In the original version of AutoCorres there was a restriction of heap lifting to
types that are also in \<^class>\<open>packed_type\<close>. Those are types that internally have no padding fields
at all. The reason was that certain lemmas especially regarding heap update become more
involved in the presence of padding fields. A \<^const>\<open>heap_update\<close> preserves the value of all
padding bytes, whereas the abstract value obtained from a corresponding \<^const>\<open>h_val\<close> is independent
of the value of the padding bytes. So in principle these notions fit together well but it
seems that some formal language was missing to reason about padding bytes. Meanwhile we added
a theory to reason about those padding bytes in @{theory \<open>AutoCorres2.Padding_Equivalence\<close>}. This
made it possible to liberate heap lifting from the restriction to \<^class>\<open>packed_type\<close>.
For example @{thm heap_update_Array} for \<^class>\<open>packed_type\<close> holds in general
@{thm heap_update_array}.
\<close>
thm heap_update_array
thm heap_update_Array

subsubsection \<open>Padding Equivalence and \<^class>\<open>xmem_type\<close>\<close>

text \<open>
Padding bytes and padding fields are introduced via the construction of new C-Types via
the combinators \<^const>\<open>ti_pad_combine\<close> and  \<^const>\<open>ti_typ_pad_combine\<close> to satisfy alignment
properties.
However, the concept of
a padding byte is not a first-class citizen of a \<^typ>\<open>('a, 'b) typ_desc\<close>, but just happens
to be a field with some special properties. In practice these fields are generated by
\<^const>\<open>ti_pad_combine\<close>, so we know that the field name starts with \<^term>\<open>''!pad''\<close>, and the
associated 'lense' for lookup and update have the 'passthrough' properties of a padding field.

We made these properties explicit by supplying a theory to identify padding-bytes in a list
of bytes associated with an C-Type, and having notions to compare such byte-lists, e.g. telling
if two byte lists are equal up-to the padding bytes, or if they agree on the padding bytes.
This information is also backed into the properties of \<^class>\<open>xmem_type\<close>, which is  a
subclass of \<^class>\<open>mem_type\<close>. All primitive word and pointer types as well as all types
that are constructed by the UMM module of the C-Parser are proved to belong to that class. The
construction of array types propagates the class as expected.

Again the notions come in pairs of a 'typed' and a 'untyped' version. The 'typed' version
associated with \<^const>\<open>typ_info_t\<close> is a lense based formalisation, the 'untyped' version
associated with \<^const>\<open>typ_uinfo_t\<close> is based on byte lists.

The lense based version is introduced by @{locale padding_lense}. Access and update
follow the approach of \<^typ>\<open>'a field_desc\<close>. Lookup / access has type \<^typ>\<open>'a \<Rightarrow> byte list \<Rightarrow> byte list\<close>.
It takes an abstract value and a supply list of padding bytes and retrieves the bytes encoding the
field. The intuition of the padding byte list is the following. It is supposed to bridge the
gap between the abstract value and the byte representation. The abstract value is independent
of the padding bytes. Hence in general there is no one-to-one correspondence between a
byte list encoding of an abstract value and the abstract value. When converting from a byte list
to an abstract value this is fine, the padding bytes are just ignored. But when we go the other
way we have to invent the padding bytes. One solution could be to just fill up with zeros. Another
solution could be to yield a non-deterministic result for the padding bytes. The UMM model
chose another way. The possible valuation for padding bytes is supplied as an additional
argument. So whenever a padding byte is needed we just take it from the position in that list.
The update has type \<^typ>\<open>byte list \<Rightarrow> 'a \<Rightarrow> 'a\<close>. It takes the value of a field, encoded as a
byte list, and transforms it to an update on the abstract value.
\<close>

context padding_lense
begin
text \<open>
The concept of a @{locale padding_lense} follows the signature of \<^typ>\<open>'a field_desc\<close> and describes the
notions of padding bytes as semantic properties of the access function \<^term>\<open>acc\<close> and the
update function \<^term>\<open>upd\<close>.
Based on them it introduces the notions of
\<^item> \<^const>\<open>is_padding_byte\<close>, is a byte a padding with respect to the lense?
\<^item> \<^const>\<open>is_value_byte\<close>, is a byte a value byte with respect to the lense,
   i.e. does the abstract value associated with the byte list depend on that byte.
\<^item> \<^const>\<open>eq_padding\<close>, access cannot distinguish the byte lists.
\<^item> \<^const>\<open>eq_upto_padding\<close>, update cannot distinguish the byte list.
\<close>
thm is_padding_byte_def
thm is_value_byte_def
thm eq_padding_def
thm eq_upto_padding_def
text \<open>
As the definitions are semantically defined the effect on \<^term>\<open>acc\<close> and \<^term>\<open>upd\<close> are rather
immediate. For example, if two byte lists are equal upto padding, then an update with \<^term>\<open>upd\<close>
yields the same result. If the padding bytes within two supply byte lists are the same, then
\<^term>\<open>acc v\<close> yields the same result for both byte lists.
\<close>
end

text \<open>
In the untyped \<^term>\<open>typ_uinfo_t\<close> we define the corresponding notions, as properties of the
byte list instead of the access and update functions.
\<^item>\<^const>\<open>is_padding_byte\<close>, a byte is a padding byte in a byte list, if normalisation
  of the byte list is independent of its value. Normalisation \<^const>\<open>norm_tu\<close> is defined on
  \<^term>\<open>typ_uinfo_t\<close> and sets all padding bytes to zero.
\<^item>\<^const>\<open>is_value_byte\<close>, normalisation depends on the value of the byte.
\<^item>\<^const>\<open>eq_padding\<close>, all padding bytes are the same.
\<^item>\<^const>\<open>eq_upto_padding\<close>, all value bytes are the same.
\<close>
thm is_padding_byte_def
thm is_value_byte_def
thm eq_padding_def
thm eq_upto_padding_def

text \<open>For instances of \<^class>\<open>xmem_type\<close> we can go back and forth between both characterisations.\<close>

thm is_padding_byte_lense_conv
thm field_lookup_is_padding_byte_lense_conv
thm is_value_byte_lense_conv
thm field_lookup_is_value_byte_lense_conv
thm eq_padding_lense_conv
thm field_lookup_eq_padding_lense_conv
thm eq_upto_padding_lense_conv
thm field_lookup_eq_upto_padding_lense_conv

text \<open>With those theorems in place it is easy to show that padding fields only consist of
padding bytes and thus do not account to the abstract value.\<close>
thm field_lookup_access_ti_to_bytes_field_conv
thm access_ti_update_ti_eq_upto_padding
thm field_lookup_qualified_padding_field_name(1)
thm is_padding_tag_def padding_tag_def padding_desc_def

subsubsection \<open>UMM-Simprocs Cache \<close>

text \<open>
To solve sideconditions on UMM-Types we have implemented some simprocs within
@{ML_structure UMM_Proofs}. Currently their scope is limited to the usecases
we have in the proofs described above. It should be straightforward to extend them
to more usecases. Their purpose is not to support abstract reasoning on types but to
provide properties of concrete instances of C-types, for example deciding whether
\<^term>\<open>TYPE(32 word) \<le>\<^sub>\<tau> TYPE(outer_C)\<close> holds.

The benefit of the simprocs is that we do not have to guess and prove lots of
lemmas already during the definition of a new UMM type, but can postpone it until we actually
need them. Once they are proven they are added to the cache, so they are only proven once.
In our use-case the lemmas we need depend on the addressable fields the user specifies on
an @{command autocorres} invocation.
\<close>

ML_val \<open>
val _ = \<^simproc>\<open>field_lookup\<close>
val _ = \<^simproc>\<open>type_calculations\<close>
val _ = \<^simproc>\<open>typuinfo_calculations\<close>
\<close>

ML_val \<open>
Cached_Theory_Simproc.trace_cache @{context}
\<close>

text \<open>
The simprocs make use of a common cache. The cache itself is implemented as a simpset.
Cache lookup means we try to rewrite with the cache:
\<^item> cache miss: term is unchanged.
\<^item> cache hit: term is changed.

In case of a cache hit we are finished and return the resulting equation. In case of a
cache miss we invoke the simplifier with a taylored simpset to derive a new equation. This
equation is then added to the cache as well as returned from the simproc.

Some fine points of this setup are related to context management. Conceptually we only prove
theory level theorems about an UMM type. So even if we prove them after the definition of the
UMM type they should all be applicable as if we have immediately proven them at the point where
the UMM type was generated.
However, the simproc is invoked in some context later on where the theory has already advanced.
In order to produce a result after a cache miss we have to somehow 'travel back in time' to the
original theory context after the definition of
the UMM type, such that the simplifier properly works on it and the result is reusable in other
contexts. We maintain that original theory state and recertify terms before simplifying them.

Another point is, that the terms we attempt to simplify and cache might depend on each other.
In order not to miss to cache intermediate results one has to carefully craft the simpsets.

In general the simplifier tries simprocs only after unconditional and conditional rules.
So when a rewrite rule has already transformed the redex the simproc will never see that redex.
This has two main implications:
\<^item> In order to have the simproc-based cache applied, there must not be a rule in the simpset that
  removes the redex before the cache actually has a chance to see it. This is why we maintain
  several simpsets to control that behaviour.
\<^item> When a cache miss was encountered and we apply the simplifier recursively to rewrite the redex
  we have to take care that the simproc is not invoked again on the same redex. When there
  is an unconditional rule in the simpset that rewrites that redex we are on the safe side. But
  beware of \<^emph>\<open>conditional\<close> rules. When the solver fails to solve the conditions the rule can fail and
  then the simproc is invoked again on the same redex. To prevent the setup from looping in these
  cases we maintain the redexes the simproc has already seen.

Here are some principles in the design of the simprocs and their simpsets:
\<^item> The type descriptions obtained by \<^const>\<open>typ_info_t\<close> are not fully expanded.
  Instead we use a simplifier setup that works on the combinators, like
   \<^const>\<open>empty_typ_info\<close>, \<^const>\<open>final_pad\<close>, \<^const>\<open>ti_typ_pad_combine\<close>. This maintains
  the more compact representation of a type-descriptor as a combinator expression, which
  is anyways the way it is originally defined.
\<^item> Fieldnames for array indexes stay symbolic: \<^term>\<open>replicate i ''1''\<close>. We employ derived
  rules for array indexes and do not have to expand the type-descriptor of arrays. For these
  rules to apply we typically need the information that the index is in the bounds of the
  array type. In those cases the simproc generates a conditional rewrite rule.
\<^item> To test equality on \<^term>\<open>export_uinfo t = export_uinfo s\<close> we normalise towards
  \<^term>\<open>export_uinfo (typ_info_t TYPE('a::c_type)) = export_uinfo (typ_info_t TYPE('b::c_type))\<close>,
  where both \<^typ>\<open>'a\<close> and \<^typ>\<open>'b\<close> are concrete instances. Then when both expressions happen
  to be the same we have proved equality. Note that this approach is incomplete and
  in particular not sufficient to disprove the equality and prove the inequality. However,
  as these equality often appears as sidecondition in a conditional rewrite rule, not being
  able to prove the equality is somehow "equivalent" to disproving it: If we cannot prove
  the sidecondition the rule cannot be applied. The most prominent pattern for this
  is a \<^const>\<open>field_lookup\<close> yielding the type-description of the selected field which is
  then compared to some type-description that is derived from a pointer type.
  To also disprove equality we make use of rule @{thm export_uinfo_eq_sub_typ_conv} and
  use the simproc on \<^const>\<open>sub_typ\<close>.
\<^item> To decide whether e.g. \<^term>\<open>TYPE(32 word) \<le>\<^sub>\<tau> TYPE(outer_C)\<close> holds or not, we first
  try to disprove it by using type name information @{thm not_sub_typ_via_td_name}.
  both \<^const>\<open>typ_name\<close> and \<^const>\<open>td_names\<close> are supplied by the UMM package:
  @{thm typ_name_simps}, @{thm td_names_simps}. By construction every distinct type
  gets an individual name.
  If that does not work we try proving it instead, by using a tansitivity prover on
  the single step sub-type relations provided by @{thm sub_typ_simps} and the
  rule for arrays @{thm  element_typ_subtyp_array_typ}.
\<close>
thm not_sub_typ_via_td_name
thm typ_name_simps
thm td_names_simps
thm sub_typ_simps
thm element_typ_subtyp_array_typ


text \<open>Here some examples\<close>
lemma "export_uinfo (typ_info_t TYPE(array_C)) = export_uinfo (typ_info_t TYPE(other_C))"
  apply simp
  oops

schematic_goal "field_lookup (typ_info_t TYPE(outer_C)) [''inner_C'', ''fld1_C''] 0 = ?X"
  apply simp
  done

lemma "TYPE(8 word) \<le>\<^sub>\<tau> TYPE(outer_C) = False"
  by simp

schematic_goal "i < 2 \<Longrightarrow> j < 3 \<Longrightarrow>
  field_ti TYPE(two_dimensional_C) [''matrix_C'', replicate i CHR ''1'', replicate j CHR ''1''] = ?X"
  apply simp
  done

lemma "TYPE(8 word) \<le>\<^sub>\<tau> TYPE(8 word[42])"
  apply simp
  done

ML_val \<open>
Cached_Theory_Simproc.trace_cache @{context}
\<close>


subsection "Examples for normalisation of array indexes"

lemma
  fixes p::"array_C ptr"
  assumes bnd[simp]: "i < 2"
  shows "(PTR(unpacked_C) &(p\<rightarrow>[''elements_C'', replicate i CHR ''1''])) = PTR(unpacked_C) &(p\<rightarrow>[''elements_C'']) +\<^sub>p int i"
  supply [[simp_trace=false, verbose=5]]
  apply (array_index_to_ptr_arith_simp)
  done


lemma
  fixes p::"array_C ptr"
  assumes bnd: "(i::32 word) < 2"
  shows "(PTR(unpacked_C) &(p\<rightarrow>[''elements_C'', replicate (unat i) CHR ''1''])) = PTR(unpacked_C) &(p\<rightarrow>[''elements_C'']) +\<^sub>p uint i"
  supply [[simp_trace=false, verbose=5]]
  apply (array_index_to_ptr_arith_simp simp: bnd)
  done


lemma
  fixes p::"array_C ptr"
  shows "do {_ <- guard (\<lambda>_. unat (i::32 word) < 2); 
     return ((PTR(unpacked_C) &(p\<rightarrow>[''elements_C'', replicate (unat i) CHR ''1''])))} =  
     do {
      _ \<leftarrow> guard (\<lambda>s. unat i < 2);
      return (PTR(unpacked_C) &(p\<rightarrow>[''elements_C'']) +\<^sub>p uint i)
    }"
  supply [[simp_trace=false, verbose=6]]
  apply array_index_to_ptr_arith_simp
  done

lemma
  fixes p::"array_C ptr"
  shows "do {_ <- guard (\<lambda>_. (i::32 word) < 2); 
     return ((PTR(unpacked_C) &(p\<rightarrow>[''elements_C'', replicate (unat i) CHR ''1''])))} =  
     do {
      _ \<leftarrow> guard (\<lambda>s. i < 2);
      return (PTR(unpacked_C) &(p\<rightarrow>[''elements_C'']) +\<^sub>p uint i)
    }"
  supply [[simp_trace=false, verbose=6]]
  apply array_index_to_ptr_arith_simp
  done

lemma
  fixes p::"array_C ptr"
  assumes bnd[simp]: "i < 2"
  shows "(PTR(unpacked_C) &(p\<rightarrow>[''elements_C'', replicate i CHR ''1'', ''chr_C''])) = 
    PTR(unpacked_C)
      &(PTR(unpacked_C) &(p\<rightarrow>[''elements_C'']) +\<^sub>p int i\<rightarrow>[''chr_C''])"
  supply [[simp_trace=false, verbose=5]]
  apply (array_index_to_ptr_arith_simp)
  done

lemma "(i::32 word) < 4  \<Longrightarrow> unat i < 4"
  supply [[array_bound_mksimps, verbose=5]]
  apply (simp)
  done

lemma "(i::32 signed word) <s 4 \<and> 0 \<le>s i \<Longrightarrow> nat (sint i) < 4"
  supply [[array_bound_mksimps, verbose=5]]
  apply (simp)
  done


subsection "Essence of Heap Lifting"

text \<open>Some birds eye view on what heap lifting is about. Consider the following C program.

\<^verbatim>\<open>
typedef struct foo {
  int myint;
  bool mybool;
} foo;

int * p;
foo * q;

(*p) = 42;
i = q->myint;
b = q->mybool;
\<close>

Is value \<open>i\<close> and \<open>b\<close> affected by update to \<open>*p\<close>

From the C-Parser we only get \<^term>\<open>c_guard p\<close> and \<^term>\<open>c_guard q\<close>:
\<^verbatim>\<open>
{c_guard p \<and> c_guard q}
(*p) = 42;
i = q->myint;
b = q->mybool;
\<close>

This only tells us something about alignment of pointers and that the pointer span does not overflow,
but nothing about disjointness of the pointer spans.

What about stronger guarantees, if we assume well-typedness of the pointers:
\<^verbatim>\<open>
{d \<Turnstile>\<^sub>t p \<and> d \<Turnstile>\<^sub>t p q}
(*p) = 42;
i = q->myint;
b = q->mybool;
\<close>

Now we know that \<open>p\<close> might alias with \<open>q->myint\<close> as they have the same type, but that pointer span
 \<open>p\<close> is actually disjoint form pointer span \<open>q->mybool\<close>.
Hence for the read of \<open>b\<close> we can skip the heap update via \<open>p\<close>.

Now consider that the structure \<open>foo\<close> is a closed structure in the split heap model. This
means that we have even stronger assumptions (which are guaranteed by guards in the lifted code):

\<^verbatim>\<open>
{root_ptr_valid d p \<and> root_ptr_valid p q}
(*p) = 42;
i = q->myint;
b = q->mybool;
\<close>

From this we can infer that the pointer spans \<open>p\<close> and the entire pointer span \<open>q\<close> don't overlap.
hence reading \<open>i\<close> as well as \<open>b\<close> can skip the heap update via \<open>p\<close>.

In general the heap lifting phase introduces the potentially weaker guards for open types:
\<^verbatim>\<open>
{ptr_valid d p \<and> ptr_valid p q}
(*p) = 42;
i = q->myint;
b = q->mybool;
\<close>

So whether \<open>i\<close> might be affected by \<open>p\<close> depends on whether field \<open>myint\<close> is addressable or not.

The essential semantic part of heap lifting is to introduce these guards at every pointer access.
In a second step these guards then allow a change in a representation from the monolitic heap
to the split heap, with a separate heap for each atomic type. But in a sense this second
step could be viewed as optional or cosmetic in the semantic sense.
There is all the information available to perform the "skipping" steps
as sketched above in the monolithic heap. This is what is performed in the simulation
proof. So the question is if we could omit introduction of "lifted globals" completely and
provide the necessary automation to the user to simplify accesses on the monolithic heap that
mimic that behaviour in the split heap. In a sense instead of doing the simulation proof upfront
it is done adhoc at every heap access / update. This avoids to provide quadratically many
commutation lemmas (in the number of fields of open types) that are introduces for the lifted globals.
\<close>

text \<open>
From the perspective of the simulation proof alone such a "virtual" split heap, which does not
introduce a new lifted-globals type, seems to be equivalent to the one which introduces a new
type with concrete distinct record fields for each fundamental heap. The simulation proof
only works when every pointer access is guarded and under that assumption the two representations
behave the same.

However, besides the simulation there are other aspects of the split heap that might pay off
for verification or further abstractions. The two models behave differently for invalid pointers:
In the split-heap (with different record fields), updates to one heap still do not
affect other heaps but we cannot properly model such updates in the monolithic heap at all.
\<close>

text \<open>
Another aspect was introduced later on for stack allocation: non-deterministic padding bytes.
The @{locale typ_heap_simulation} was generalised to state that lifting to the split heap is
invariant for arbitrary padding bytes, i.e. @{locale write_simulation}. The lifted heap only
cares about the abstract values were the values of the padding bytes become irrelevant.
\<close>
thm h_val_heap_update_padding
thm plift_heap_update_padding_heap_update_pointless_conv
thm lift_heap_update_padding_heap_update_conv

context open_struct_all_corres
begin
thm ts_def
thm ac_corres
end
end


