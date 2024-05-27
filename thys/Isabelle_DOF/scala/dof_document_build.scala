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

/*** document build engine for Isabelle/DOF ***/

package isabelle.dof

import isabelle._


object DOF_Document_Build
{
  class Engine extends Document_Build.Bash_Engine("dof")
  {
    def the_document_entry(context: Document_Build.Context, name: String): Export.Entry = {
      val entries =
        for {
          node_name <- context.all_document_theories
          entry <- context.session_context.get(node_name.theory, name)
        } yield entry

      entries match {
        case List(entry) => entry
        case Nil =>
          error("Missing export " + quote(name) + " for document theories of session " +
            quote(context.session))
        case dups =>
          error("Multiple exports " + quote(name) + " for theories " +
            commas_quote(dups.map(_.theory_name).sorted.distinct))                   
      }
    }

    override def prepare_directory(
      context: Document_Build.Context,
      dir: Path,
      doc: Document_Build.Document_Variant,
      verbose: Boolean): Document_Build.Directory =
    {
      val options = DOF.options(context.options)
      val latex_output = new Latex_Output(options)
      val directory = context.prepare_directory(dir, doc, latex_output, verbose)

      val isabelle_dof_dir = context.session_context.sessions_structure(DOF.session).dir

      val ltx_ontologies = split_lines((the_document_entry(context, "dof/use_ontology")).text)

      // LaTeX styles from Isabelle/DOF directory
      (List(Path.explode("latex/styles"), Path.explode("ontologies")) :::(ltx_ontologies.map(name => 
              context.session_context.sessions_structure((Long_Name.base_name(Long_Name.qualifier(name))).mkString).dir))) 
        .flatMap(dir => File.find_files((isabelle_dof_dir + dir).file, _.getName.endsWith(".sty")))
        .foreach(sty => Isabelle_System.copy_file(sty, directory.doc_dir.file))

      // ontologies.tex from session exports
      File.write(directory.doc_dir + Path.explode("ontologies.tex"),
           ltx_ontologies.map(name => "\\usepackage{DOF-" + Long_Name.base_name(name) + "}\n").mkString)

      // root.tex from session exports
      File.write(directory.doc_dir + Path.explode("root.tex"),
        (the_document_entry(context, "dof/use_template")).text)

      // dof-config.sty
      File.write(directory.doc_dir + Path.explode("dof-config.sty"), """
\newcommand{\isabelleurl}{""" + DOF.isabelle_url + """}
\newcommand{\dofurl}{""" + DOF.url + """}
\newcommand{\dof@isabelleversion}{""" + DOF.isabelle_version + """}
\newcommand{\isabellefullversion}{""" + DOF.isabelle_version + """\xspace}
\newcommand{\dof@version}{""" + DOF.version + """}
\newcommand{\dof@artifacturl}{""" + DOF.artifact_url + """}
\newcommand{\doflatestversion}{""" + DOF.latest_version + """}
\newcommand{\isadoflatestdoi}{""" + DOF.latest_doi + """}
\newcommand{\isadofgenericdoi}{""" + DOF.generic_doi + """}
\newcommand{\isabellelatestversion}{""" + DOF.latest_isabelle + """}
""")


      val texinputs: Path = Path.explode("~~/lib/texinputs")
      val comment_latex = options.bool("document_comment_latex")
      if (!comment_latex) { 
        Isabelle_System.copy_file(texinputs + Path.basic("comment.sty"), directory.doc_dir)
      }

      doc.tags.sty(comment_latex).write(directory.doc_dir)


      directory
    }
  }

  class Latex_Output(options: Options) extends Latex.Output(options)
  {
    override def latex_environment(
      name: String,
      body: Latex.Text,
      optional_argument: String = ""): Latex.Text =
    {
      XML.enclose(
        "\n\\begin{" + name + "}" + optional_argument + "\n",
        "\n\\end{" + name + "}", body)
    }
  }
}
