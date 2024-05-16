(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


\<^if_ARM>\<open>structure ImplementationNumbers = ImplementationNumbersARM;\<close>
\<^if_ARM64>\<open>structure ImplementationNumbers = ImplementationNumbersARM64;\<close>
\<^if_ARM_HYP>\<open>structure ImplementationNumbers = ImplementationNumbersARM_HYP;\<close>
\<^if_RISCV64>\<open>structure ImplementationNumbers = ImplementationNumbersRISCV64;\<close>
\<^if_X64>\<open>structure ImplementationNumbers = ImplementationNumbersX64;\<close>