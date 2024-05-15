/*
 * Copyright (c) 
 *               2021-2022 The University of Exeter. 
 *               2021-2022 The University of Paris-Saclay. 
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


/*** constants and parameters for Isabelle/DOF ***/

package isabelle.dof

import isabelle._


object DOF {
  /** parameters **/

  val isabelle_version = "2023"
  val isabelle_url = "https://isabelle.in.tum.de/website-Isabelle2023" 

  val afp_version = "afp-2023-09-13"

  // Isabelle/DOF version: "Unreleased" for development, semantic version for releases
  val version = "Unreleased"

  val session = "Isabelle_DOF"
  val session_ontologies = "Isabelle_DOF-Ontologies"

  val latest_version = "1.3.0"
  val latest_isabelle = "Isabelle2021-1"
  val latest_doi = "10.5281/zenodo.6810799"
  val generic_doi = "10.5281/zenodo.3370482"

  // Isabelle/DOF source repository
  val url = "https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF/src/branch/Isabelle_dev"

  // Isabelle/DOF release artifacts
  val artifact_dir = "releases/Isabelle_DOF/Isabelle_DOF"
  val artifact_host = "artifacts.logicalhacking.com"
  val artifact_url: String = "https://" + artifact_host + "/" + artifact_dir

  def options(opts: Options): Options = opts + "document_comment_latex"



  /** Isabelle tool wrapper **/

  sealed case class Parameter(name: String, value: String) {
    override def toString: String = name

    def print(value_only: Boolean): String =
      if (value_only) value else name + "=" + value
  }

  val parameters: List[Parameter] =
    List(
      Parameter("isabelle_version", isabelle_version),
      Parameter("afp_version", afp_version),
      Parameter("dof_version", version)
    ).sortBy(_.name)

  def print_parameters(names: List[String],
    all: Boolean = false,
    value_only: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val bad = names.filter(name => !parameters.exists(_.name == name))
    if (bad.nonEmpty) error("Unknown parameter(s): " + commas_quote(bad))

    val params = if (all) parameters else parameters.filter(p => names.contains(p.name))
    for (p <- params) progress.echo(p.print(value_only))
  }

  val isabelle_tool = Isabelle_Tool("dof_param", "print Isabelle/DOF parameters",
    Scala_Project.here, args =>
  {
    var all = false
    var value_only = false

    val getopts = Getopts("""
Usage: isabelle dof_param [OPTIONS] NAMES

  Options are:
    -a           print all parameters
    -b           print values only (default: NAME=VALUE)

  Print given Isabelle/DOF parameters, with names from the list:
  """ + commas_quote(parameters.map(_.toString)),
      "a" -> (_ => all = true),
      "b" -> (_ => value_only = true))

    val names = getopts(args)
    if (names.isEmpty && !all) getopts.usage()

    print_parameters(names, all = all, value_only = value_only, progress = new Console_Progress)
  })
}
