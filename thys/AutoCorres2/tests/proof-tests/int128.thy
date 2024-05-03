(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory int128
  imports AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "int128.c"

autocorres [skip_word_abs] "int128.c"

context int128_all_corres
begin

lemma "u' i j \<equiv> UCAST(32 \<rightarrow> 128) i * UCAST(32 \<rightarrow> 128) j"
  by (fact u'_def)

lemma "i' i j \<equiv>
   do {
  _ \<leftarrow> oguard
        (\<lambda>s. - 170141183460469231731687303715884105728
              \<le> sint (SCAST(32 signed \<rightarrow> 128 signed) i) * sint (SCAST(32 signed \<rightarrow> 128 signed) j) \<and>
              sint (SCAST(32 signed \<rightarrow> 128 signed) i) * sint (SCAST(32 signed \<rightarrow> 128 signed) j)
              \<le> 170141183460469231731687303715884105727);
  oreturn (UCAST(32 \<rightarrow> 128 signed) (SCAST(32 signed \<rightarrow> 32) i * SCAST(32 signed \<rightarrow> 32) j))
}"
  by (fact i'_def)

end

end