### input templates

# string which will be replaced by output of a generator
# $ denotes an (optional) parameter for the generator
magic_str = u"<!--gen$-->"

# pattern for release tarball filename
release_pattern = """^afp-(.*)-([0-9\-]{10}).tar.gz$"""

# suffix of files which will be considered as template
template_suffix = ".tpl"

# suffix of a template file will be replaced by this suffix
output_suffix = ".shtml"


### html output

# wrapper for a link list of entries
# {0}: link list
html_topic_link_list = u"""<div class="list">\n{0}</div>\n\n"""

# template for a single link to an entry on topic page, where
# filename is the same as the display name
# {0}: filename (without .shtml suffix) relative to 'entries' directory
html_topic_link = u"""<a href="entries/{0}.shtml">{0}</a> &nbsp;\n"""

# list of headings
# {0}: display name of heading
html_topic_headings = [ u"<h2>{0}</h2>\n\n", u"<h3>{0}</h3>\n\n", u"\n<strong>{0}:</strong>&nbsp;" ]

# denotes the heading level (beginning with 0), after which no
# separate html_topic_link_list will be created
html_until_level = 1

# link to an author
# {0}: url
# {1}: display name
html_author_link = u"""<a href="{0}">{1}</a>"""

# disclaimer for devel index page
html_index_devel = u"""
  <strong>
  This is the development version of the archive, referring to a recent
  Isabelle development version. Some entries may not be in a working state, see
  the <a href="status.shtml">status page</a> for more information.
  The main archive is available from the <a href="http://www.isa-afp.org">front page</a>.
  </strong>
"""

# standard header for stable AFP
html_index_stable = u"""
  A <a href="http://devel.isa-afp.org">development version</a> of the archive is available as well.
"""

# wrapper for each year's entries displayed on index page
# {0}: year in YYYY format
# {1}: entries
html_index_year = u"""
<p>&nbsp;</p>
<table width="80%" class="entries">
  <tbody>
    <tr>
	  <td class="head">{0}</td>
	</tr>

{1}

  </tbody>
</table>
"""

# template for an entry displayed on index page
# {0}: date in YYYY-MM-HH format
# {1}: filename (without .shtml suffix) relative to 'entries' directory
# {2}: display name
# {3}: list of html_author_link, comma-separated
html_index_entry = u"""<tr><td class="entry">\n{0}:\n<a href="entries/{1}.shtml">{2}</a>\n<br>Author:\n{3}\n</td></tr>\n\n"""

# template for an entry displayed on status page
# {0}: status string
# {1}: filename (without .shtml suffix) relative to 'entries' directory
html_status_entry = u"""<tr><td class="status-{0}">[{0}]</td><td class="entry"><a href="entries/{1}.shtml">{1}</a></td></tr>\n"""

# heading wrapper on entry page
html_entry_heading = u"<h1>{0}</h1>\n<p></p>"

# capitalized word in heading on entry page
# {0}: first character
# {1}: other characters
html_entry_capitalized = u"""<font class="first">{0}</font>{1}\n"""

# link to license text
# {0}: display title
# {1}: url
html_license_link = u"""<a href="{1}">{0}</a>"""

# link to another entry
# {0}: display title
# {1}: url
html_entry_link = u"""<a href="{1}">{0}</a>"""

# wrapper for a text column in header
# {0}: title (e. g. 'Change history')
# {1}: text
html_entry_text_wrapper = u"""
    <tr><td class="datahead" valign="top">{0}:</td>
        <td class="abstract">
{1}
        </td></tr>
"""

# wrapper for a pre-formatted text column in header
# {0}: title (e. g. 'BibTeX')
# {1}: text
html_entry_pre_text_wrapper = u"""
    <tr><td class="datahead" valign="top">{0}:</td>
        <td class="formatted">
			<pre>{1}</pre>
        </td></tr>
"""

# wrapper for contributors line
# {0} formatted contributors list
html_contributors = u"""
	<tr><td class="datahead">Contributors:</td>
        <td class="data">{0}</td></tr>
"""

# wrapper for the entry header
# {0}: title
# {1}: author
# {2}: contributors
# {3}: date
# {4}: text columns (html_entry_text_wrapper)
# {5}: license
# {6}: entry
# {7}: depends-on (html_entry_depends_on_wrapper)
# {8}: used-by (html_entry_used_by_wrapper)
# {9}: status (html_entry_status_wrapper)
# {{...}} is for escaping, because Py's format syntax collides with SSI
html_entry_header_wrapper = u"""
<table width="80%" class="data">
  <tbody>
    <tr><td class="datahead" width="20%">Title:</td>
        <td class="data" width="80%">{0}</td></tr>

    <tr><td class="datahead">Author:</td>
        <td class="data">{1}</td></tr>
{2}
    <tr><td class="datahead">Submission date:</td>
        <td class="data">{3}</td></tr>
{4}
    <tr><td class="datahead">License:</td>
        <td class="data">{5}</td></tr>
{7}
{8}
{9}

  </tbody>
</table>

<p></p>

<!--#set var="name" value="{6}" -->
<!--#set var="binfo" value="../browser_info/current/AFP/${{name}}" -->
"""

html_entry_depends_on_wrapper = u"""

    <tr><td class="datahead">Depends on:</td>
        <td class="data">{0}</td></tr>
"""

html_entry_used_by_wrapper = u"""

    <tr><td class="datahead">Used by:</td>
        <td class="data">{0}</td></tr>
"""

# wrapper for the entry status
# {0}: status
html_entry_status_wrapper = u"""

    <tr><td class="status-{0}">Status: [{0}]</td>
        <td class="data">This is a development version of this entry. It might change over time and is not stable. Please refer to release versions for citations.</td></tr>
"""

# list wrapper for older releases
# {0}: list entries
html_entry_older_list = u"<ul>\n{0}\n</ul>"

# wrapper for older releases
html_entry_older_wrapper = u"""
    <tr><td class="links">Older releases: {0}
    </td></tr>
"""

# list entry for older releases
# {0}: isabelle release (e. g. "2009")
# {1}: release date (e. g. "2009-04-29")
html_entry_older_release = u"""<li>Isabelle {0}: <a href="../release/afp-<!--#echo var="name" -->-{1}.tar.gz">afp-<!--#echo var="name" -->-{1}.tar.gz</a></li>\n"""

# wrapper for bibtex output
# {0}: key
# {1}: title
# {2}: author
# {3}: month
# {4}: year
# {{...}} is for escaping, because Py's format syntax collides with SSI
bibtex_wrapper = u"""@article{{{0}-AFP,
  author  = {{{1}}},
  title   = {{{2}}},
  journal = {{Archive of Formal Proofs}},
  month   = {3},
  year    = {4},
  note    = {{\\url{{http://isa-afp.org/entries/{0}.shtml}},
            Formal proof development}},
  ISSN    = {{2150-914x}},
}}"""

# stable download link
html_download_stable = u"""
  <tr><td class="head"><b>Current stable version</b> (for current Isabelle release):</td></tr>
    <tr></tr><td class="entry">[<!--#include file="release-date.txt"-->]:
    <a href="release/afp-current.tar.gz"><tt>afp-<!--#include file="release-date.txt"-->.tar.gz</tt></a>
  </td></tr>
"""


### licenses

# key : (title, url)
#   'key' denotes the short name of the license (e. g. 'LGPL')
#   'title' denotes the display title of the license (e. g. 'GNU Lesser General Public License (LGPL)')
#   'url' contains the url of the license text

licenses = {
	'LGPL': ("GNU Lesser General Public License (LGPL)", "http://isa-afp.org/LICENSE.LGPL"),
	'BSD': ("BSD License", "http://isa-afp.org/LICENSE"),
}


### options

class Options(object):
	def __init__(self):
		self.enable_debug = False
		self.enable_warnings = True
		self.dest_dir = None
		self.do_check = False
		self.metadata_dir = None
		self.status_file = None
	
	def is_devel(self):
		return self.status_file is not None

options = Options()
