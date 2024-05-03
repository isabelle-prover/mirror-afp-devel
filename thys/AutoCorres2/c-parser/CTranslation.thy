(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CTranslation
  imports
  CTranslationSetup
  Array_Selectors
keywords
  "new_C_include_dir":: thy_decl
and
  "include_C_file"
  "install_C_types"
  "install_C_file" :: thy_load

begin
  ML_file "isar_install.ML"

end
