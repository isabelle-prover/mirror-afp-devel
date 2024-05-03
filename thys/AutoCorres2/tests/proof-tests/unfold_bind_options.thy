(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory unfold_bind_options
imports "AutoCorres2_Main.AutoCorres_Main"
begin



install_C_file "unfold_bind_options.c"

text \<open>

This theory demonstrates the autocorres option \<open>unfold_constructor_bind\<close>, which allows
to tweak the behaviour of expanding certain 'simple' assignments which manifest in 'bind' variants.

Unfolding the bind can trigger simplifications later on in the code (e.g. guards). As 
a drawback the correspondence to the original C code gets obfuscated, as intermediate assignments
disappear.

Currently the following heuristics is implemented:
\<^item> If the assigned value is atomic the bind is unfolded
\<^item> If the assigned value is only used once in the following code it is unfolded.
\<^item> If none of the above rules triggered and the assigned value is a compound C type (aka struct) then
  \<^item> In case it is a constructor expression the option \<open>unfold_constructor_bind\<close> is used.
    \<^item> Never: the bind in not unfolded.
    \<^item> Always: the bind is always unfolded.
    \<^item> Selectors: the bind is unfolded if the constructor is only applied to field-selectors. This
      is the default option.
  \<^item> In case it is an update-expression then the bind is unfolded if it is only applied to the
    corresponding field-selector.

This is immplemented via a simproc: @{ML L2Opt.l2_marked_gets_bind_simproc'}
\<close>



autocorres [scope = add add3] "unfold_bind_options.c"


context ts_definition_add3
begin
thm ts_def
end

text \<open>Here we demonstrate the case were the assigned value is only used once. Even if
the option is \<open>Never\<close> the bind gets unfolded.\<close>
autocorres [scope = single, unfold_constructor_bind = Never] "unfold_bind_options.c"
context ts_definition_single
begin
lemma "single' inner \<equiv> add' (fld1_C inner) 1" 
  by (simp add: ts_def)
end


text \<open>Here the constructor is only used with field selectors, hence the bind gets unfolded
with option \<open>Selectors\<close>, which is also the default option.\<close>
autocorres [scope = foo_selectors, unfold_constructor_bind=Selectors] "unfold_bind_options.c"
context ts_definition_foo_selectors
begin
lemma "foo_selectors' inner \<equiv> add' (fld1_C inner) 0x2A"
  by (simp add: ts_def)
end

text \<open>You can force unfolding by setting the option to \<open>Always\<close>. Note that the resulting
function is in the "pure"-monad. The "bind" became a "let" in the final outcome.\<close>
autocorres [scope = foo_never, unfold_constructor_bind=Never] "unfold_bind_options.c"
context ts_definition_foo_never
begin
lemma "foo_never' inner \<equiv>
  let my_inner = inner_C (fld1_C inner) 0x2A
  in add' (fld1_C my_inner) (fld2_C my_inner)"
  by (simp add: ts_def)
end

text \<open>We can surpress the unfolding by setting the option to \<open>Never\<close>.\<close>
autocorres [scope = foo_never, unfold_constructor_bind = Never] "unfold_bind_options.c"
context ts_definition_foo_never
begin
lemma "foo_never' inner \<equiv>
  let my_inner = inner_C (fld1_C inner) 0x2A
  in add' (fld1_C my_inner) (fld2_C my_inner)"
  by (simp add: ts_def)
thm ts_def 
end

text \<open>Here is an example where the constructor is not only applied to selectors, but passed
down to a function. The bind is hence not unfolded by default (option \<open>Selectors\<close>) \<close>
autocorres [scope = bar_selectors, unfold_constructor_bind = Selectors] "unfold_bind_options.c"

context ts_definition_bar_selectors
begin
thm bar_selectors'_def
lemma "bar_selectors' inner \<equiv>
  let my_inner = inner_C (fld1_C inner) 0x2A
  in add3' 1 my_inner + add3' 2 my_inner"
  by (simp add: ts_def)
end

text \<open>You can force unfolding by setting the option to \<open>Always\<close>.\<close>
autocorres [scope = bar_always, unfold_constructor_bind = Always] "unfold_bind_options.c"
context ts_definition_bar_always
begin
lemma "bar_always' inner \<equiv>
  add3' 1 (inner_C (fld1_C inner) 0x2A) +
  add3' 2 (inner_C (fld1_C inner) 0x2A)"
  by (simp add: ts_def)
end

end
