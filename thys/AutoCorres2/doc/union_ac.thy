(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Unions"
theory union_ac
  imports 
   "AutoCorres"
 
begin

subsection \<open>Union support in C-Parser and Autocorres\<close>

text \<open>
Fully fledged C unions can have a lot of semantic subtleties in particular with respect to
undefined behavior when it comes to different padding in the variants, effective types and accessing 
the union via different variants, e.g. writing a pointer through one variant and subsequently 
reading or writing the same union via another variant. 
See for example \<^url>\<open>https://robbertkrebbers.nl/research/thesis.pdf\<close> in subsections 2.5.5 ff. for
a discussion of some fine points.

Our current solution is very pragmatic by only supporting a subset of unions that does not exhibit
the more "weired" behaviours:
\<^item> Single variant unions
\<^item> Multi-variant unions where each variant is packed (no implicit padding) and has the same size.

For these limited unions the semantics is deterministic and basically boils down to casting / coercing different 
C-types. Note that every @{class c_type} is equipped with conversions @{const from_bytes} and @{const to_bytes}
which allows us to take a value, convert it to a byte list and then make another value 
(potentially with a different type) from that byte list again. So the basic machinery is already there.

The C parser analyses which variants of a union are actually actively used in the code you want to verify.
Only those variants (internally referred to as active variants) are taken into account. If there
is only a single variant we are fine and a single record type is constructed in HOL as the C-type
representing that type. It is the same construction as for a structure type of that variant.

In case there are multiple active variants the C parser checks that all those variants have the
same size and are \<^emph>\<open>packed\<close> which means that there is no padding. The original C code
might have to be rewritten with explicit padding fields to fulfill this requirement.

We create a record type for each variant of the union, like a 'struct' for each variant. One 
variant is considered as the \<^emph>\<open>canonical\<close> variant. Currently this always is the first variant of
the union. The idea of the canonical variant is that every access or update to a union is always
done via this canonical variant and then 'casted' to the variant you need. This casting is implemented
via @{const ptr_coerce} for pointers and @{const coerce} and @{const coerce_map} for values.

Example: 

\<^verbatim>\<open>
typedef struct {
  unsigned fst;
  unsigned snd;
 } unsigned_pair;

typedef struct {
  signed fst;
  signed snd;
 } signed_pair;


typedef union {
  unsigned_pair u;
  signed_pair s;
} open_union;
\<close>

The union \<open>open_union\<close> has two variants. The first one \<open>u\<close> is considered to be the canonical one. 
So when you want to update a variant \<open>s\<close> in the heap via a pointer to \<open>open_union\<close> we first read the 
canonical variant \<open>u\<close> from the heap then coerce the value to a variant \<open>s\<close>, then the update on the 
value is performed then the resulting value is coerced back to variant \<open>u\<close> and finally written 
back to the heap.

A good mental model for this implementation is that accesses to unions are normalised towards the
canonical variants of the root pointers. This also carries over to the split heap model you obtain
when you perform the HL phase of autocorres. There is only one relevant heap for the union, which
is the heap for the canonical variant. This means that you can also define \<open>addressable_fields\<close> for
the canonical variant. Currently you cannot define \<open>addressable_fields\<close> for the other variants.
\<close>


include_C_file "union.h" for union.c
install_C_file "union.c" 
autocorres [addressable_fields = open_union.u]union.c

context union_all_corres 
begin
thm ts_def
thm l2_def
subsubsection \<open>Names\<close>

text \<open>The union \<open>open_union\<close> has two variants \<open>u\<close> and \<open>s\<close>. The first one, \<open>u\<close>, is considered
to be the canonical one. The corresponding c-type becomes "THE" type of union and is named
@{typ open_union_C}. The other variant \<open>s\<close> gets the qualified name @{typ "open_union_C's_C"}. \<close>

term open_union_C
term u_C
thm u_C_def
term u_C_update
thm u_C_update_def

term open_union_C's_C
term s_C
thm s_C_def
term s_C_update
thm s_C_update_def

term heap_open_union_C
thm heap_open_union_C_def

subsubsection "Anonymous Structures and Union"

text \<open>For anonymous structures and types we create names by considering the surrounding typedef
and structure / union. For example see the typedef of \<open>my_union\<close>. The canonical variant
for the union gets @{typ my_union_C}. The variant \<open>f\<close> is an anonymous structure. The type of
the anonymous structure is type @{typ "my_union_C'f_C'struct"}, whereas the type of the variant \<open>f\<close>
is @{typ "my_union_C'f_C"}. Analogously there is also a suffix \<open>union\<close> in case of an 
anoymous union. Note the naming convention: 
For nested names note that sufffix \<open>union\<close> or \<open>struct\<close> is for the nested union or structure itself, in 
contrast to the name without suffix which denotes the variant of the enclosing union.
\<close>

typ my_union_C
term my_union_C

typ my_union_C'f_C'struct
term "f1_C"
thm "f1_C_def"

typ my_union_C'f_C
term "f_C"
thm "f_C_def"

typ my_union_C'g_C'union
term "x1_C"
thm "x1_C_def"

typ my_union_C'g_C
term "g_C"
thm "g_C_def"

subsubsection \<open>Lemmas to coerce values / heap accesses\<close>

thm coerce_id
thm coerce_cancel_packed
thm coerce_map_id
thm coerce_coerce_map_cancel_packed

thm h_val_coerce_ptr_coerce_packed
thm h_val_field_ptr_coerce_from_bytes_packed
thm heap_update_field_ptr_coerce_from_bytes_packed
thm heap_state.L2_modify_heap_update_ptr_coerce_packed_conv
thm heap_state.L2_modify_heap_update_ptr_coerce_packed_field_root_conv
thm L2_modify_heap_update_field_root_conv

end



end