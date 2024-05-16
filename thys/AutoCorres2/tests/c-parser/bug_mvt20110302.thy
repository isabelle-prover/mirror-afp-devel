(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bug_mvt20110302
imports "AutoCorres2.CTranslation"
begin

install_C_file "bug_mvt20110302.c"

context bug_mvt20110302_simpl
begin

  thm create_ipcbuf_frame_body_def
end

end
