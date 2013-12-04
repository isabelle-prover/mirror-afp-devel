#!/usr/bin/env python
# vim: set fileencoding=utf-8 :

##
## Dependencies: Python 2.7
## 
## This script reads a metadata file and generates the topics.shtml,
## index.shtml and the entry pages on afp.sf.net.
## 
## For meta data documentation see ../metadata/README
## For adding new entries see ../doc/editors/new-entry-checkin.html
## 

from collections import OrderedDict
from optparse import OptionParser
from sys import argv, stderr
from functools import partial
import codecs
import ConfigParser
import os
import re
from termcolor import colored

# global config

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

# wrapper for the entry header
# {0}: title
# {1}: author
# {2}: date
# {3}: text columns (html_entry_text_wrapper)
# {4}: license
# {5}: entry
# {6}: depends-on
# {{...}} is for escaping, because Py's format syntax collides with SSI
html_entry_header_wrapper = u"""
<table width="80%" class="data">
  <tbody>
    <tr><td class="datahead" width="20%">Title:</td>
        <td class="data" width="80%">{0}</td></tr>

    <tr><td class="datahead">Author:</td>
        <td class="data">{1}</td></tr>

    <tr><td class="datahead">Submission date:</td>
        <td class="data">{2}</td></tr>
{3}
    <tr><td class="datahead">License:</td>
        <td class="data">{4}</td></tr>
{6}

<!--#set var="status" value="-STATUS-" -->
<!--#set var="version" value="-VERSION-" -->
<!--#set var="afp-version" value="-AFPVERSION-" -->
<!---INCLUDE- file="devel-warning.shtml"-->

  </tbody>
</table>

<p></p>

<!--#set var="name" value="{5}" -->
<!--#set var="binfo" value="../browser_info/current/AFP/${{name}}" -->
"""

html_entry_depends_on_wrapper = u"""

    <tr><td class="datahead">Depends on:</td>
        <td class="data">{0}</td></tr>
"""

# list wrapper for older releases
# {0}: list entries
html_entry_older_list = u"<ul>\n{0}\n</ul>"

# list entry for older releases
# {0}: isabelle release (e. g. "2009")
# {1}: release date (e. g. "2009-04-29")
html_entry_older_release = u"""<li>Isabelle {0}: <a href="../release/afp-<!--#echo var="name" -->-{1}.tar.gz">afp-<!--#echo var="name" -->-{1}.tar.gz</a></li>\n"""

### html output

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
  note    = {{\\url{{http://afp.sf.net/entries/{0}.shtml}},
            Formal proof development}},
  ISSN    = {{2150-914x}},
}}"""


### metadata format

# key : (split, processor, default)
#   'key' denotes the key of the key-value pair in the metadata file
#     if it ends with a '*', e. g. 'extra*' and you have two keys 'extra-foo'
#     and 'extra-bar' in your metadata file, you will get:
#       attributes['extra'] == { 'foo': <data>, 'bar': <data> }
#   'split' if False, the value will be treated as a  simple string, otherwise
#     it will be split at ','
#   'processor' if defined, the function with this name will be called with
#     each string (or substring if split is not None) and the result is used
#     (notice: must be a string, because the functions are defined later in source)
#   'default' is optional and specifies a default value, which will be treated
#     as if it has been read from the file, i. e. is subject to splitting and
#     processing
attribute_schema = {
	'topic': (True, None, None),
	'date': (False, None, None),
	'author': (True, "parse_author", None),
	'title': (False, None, None),
	'abstract': (False, None, None),
	'license': (False, "parse_license", "BSD"),
	'ignore': (True, None, ""),
	'extra*': (False, "parse_extra", None),
	'depends-on': (False, "parse_depends_on", ""),
}

### licenses

# key : (title, url)
#   'key' denotes the short name of the license (e. g. 'LGPL')
#   'title' denotes the display title of the license (e. g. 'GNU Lesser General Public License (LGPL)')
#   'url' contains the url of the license text

licenses = {
	'LGPL': ("GNU Lesser General Public License (LGPL)", "http://afp.sourceforge.net/LICENSE.LGPL"),
	'BSD': ("BSD License", "http://afp.sourceforge.net/LICENSE"),
}

### template files

# key : (path, generator, for-each)
#   'key' denotes the filename of the template (without suffix)
#   'path' denotes the destination sub-path for generated files
#   'generator' denotes the name of the generating function for the data of the
#     template. The parameters this function will get is determined by 'for-each'.
#     You may also assume that this function never gets any ignored entry.
#   'for-each' determines generation behaviour: if set to None, one file
#     will be generated for all entries together and the 'generator' function will
#     receive a list of all entries. Otherwise, a function expression
#     is expected which gets the entry name and returns a filename to store the
#     result in (without suffix) and the 'generator' function will get just one
#     entry name and its attributes
templates = {
	'topics': ('.', "generate_topics", None),
	'index': ('.', "generate_index", None),
	'entry': ('./entries', "generate_entry", lambda entry: entry)
}

# end global config

class Tree(object):
	def __init__(self):
		self.subtopics = OrderedDict()
		self.entries = []

	def add_topic(self, topic):
		if len(topic) > 0:
			if topic[0] not in self.subtopics:
				tree = Tree()
				self.subtopics[topic[0]] = tree
			else:
				tree = self.subtopics[topic[0]]
			tree.add_topic(topic[1:])

	def add_to_topic(self, topic, entry):
		if len(topic) > 0:
			if topic[0] not in self.subtopics:
				warn(u"In entry {0}: unknown (sub)topic {1}".format(entry, topic))
			else:
				self.subtopics[topic[0]].add_to_topic(topic[1:], entry)
		else:
			self.entries.append(entry)

	def __str__(self):
		return self._to_str()

	def _to_str(self, indent = 0):
		indent_str = ' ' * indent
		result = indent_str + str(self.entries) + "\n"
		for subtopic, tree in self.subtopics.items():
			result += indent_str
			result += subtopic
			result += "\n"
			result += tree._to_str(indent + 2)
		return result

class Stats(object):
	def __init__(self):
		self.tpls = 0
		self.failed_tpls = 0
		self.gens = 0
		self.failed_gens = 0
	
	def __str__(self):
		failed_tpl_str = "({0!s} failed)".format(self.failed_tpls) if self.failed_tpls > 0 else ""
		failed_gen_str = "({0!s} failed)".format(self.failed_gens) if self.failed_gens > 0 else ""

		success_tpl_str = "Successfully read {0!s} template(s)".format(self.tpls - self.failed_tpls)
		success_gen_str = "Successfully written {0!s} file(s)".format(self.gens - self.failed_gens)

		return "{0} {1}\n{2} {3}".format(
			colored(success_tpl_str, 'green', attrs=['bold']),
			colored(failed_tpl_str, 'red', attrs=['bold']),
			colored(success_gen_str, 'green', attrs=['bold']),
			colored(failed_gen_str, 'red', attrs=['bold'])
		)

def debug(message, indent = 0, title = ""):
	if options.enable_debug:
		if isinstance(message, list):
			debug(title + ": [" if title else "[", indent)
			for line in message:
				debug(line, indent + 2)
			debug("]", indent)
		elif isinstance(message, dict):
			debug(title + ": {" if title else "{", indent)
			for key, value in message.items():
				debug(u"{0} -> {1}".format(key, value), indent + 2)
			debug("}", indent)
		else:
			if title:
				print >> stderr, (u"Debug: {0}{1}: {2}".format(' ' * indent, title, message))
			else:
				print >> stderr, (u"Debug: {0}{1}".format(' ' * indent, message))

def warn(message):
	if options.enable_warnings:
		print >> stderr, (colored(u"Warning: {0}".format(message), 'yellow', attrs=['bold']))

def notice(message):
	if options.enable_warnings:
		print >> stderr, (u"Notice: {0}".format(message))

def error(message, exception = None, abort = False):
	print >> stderr, (colored(u"Error: {0}".format(message), 'red', attrs=['bold']))
	if exception:
		error("*** exception message:")
		error(u"*** {0!s} {1!s}".format(exception, type(exception)))
	if abort:
		error("Fatal. Aborting")
		exit(1)

# performs a 'diff' between metadata and the actual filesystem contents
def check_fs(meta_entries, directory):
	fs_entries = set(e for e in os.listdir(directory) if os.path.isdir(os.path.join(directory, e)))
	meta_entries = set(k for k, _ in meta_entries.items())
	# check for entries not existing in filesystem
	for fs_missing in meta_entries - fs_entries:
		print >> stderr, (colored(u"Check: In metadata: entry {0} doesn't exist in filesystem".format(fs_missing), 'yellow', attrs=['bold']))
	for meta_missing in fs_entries - meta_entries:
		print >> stderr, (colored(u"Check: In filesystem: entry {0} doesn't exist in metadata".format(meta_missing), 'yellow', attrs=['bold']))
	return len(fs_entries ^ meta_entries)

# takes the 'raw' data from metadata file as input and performs:
# * checking of data against attribute_schema
# * defaults for missing keys
# * elimination of extraneous keys
# * splitting at ',' if an array is requested
def validate(entry, attributes):
	sane_attributes = {}
	missing_keys = []
	processed_keys = set()
	for key, (split, processor_str, default) in attribute_schema.items():
		if processor_str:
			if processor_str in globals():
				processor = globals()[processor_str]
			else:
				error(u"In metadata: For key {0}: processor function {1} doesn't exist".format(key, processor_str), abort = True)
		else:
			processor = lambda str, **kwargs: str
		if key.endswith("*"):
			shortkey = key[:len(key)-1]
			result = OrderedDict()
			process = partial(processor, entry = entry, shortkey = shortkey)
			for appkey, str in attributes.items():
				if appkey.startswith(shortkey + "-"):
					processed_keys.add(appkey)
					app = appkey[:len(shortkey)]
					if not split:
						result[app] = process(str.strip(), appendix = app)
					else:
						result[app] = [process(s.strip(), appendix = app) for s in str.split(',')]
			sane_attributes[shortkey] = result
		else:
			process = partial(processor, entry = entry, key = key)
			if default == None and key not in attributes:
				missing_keys.append(key)
				sane_attributes[key] = process("") if not split else []
			else:
				value = attributes[key] if key in attributes else default
				processed_keys.add(key)
				if not split:
					sane_attributes[key] = process(value)
				else:
					sane_attributes[key] = [process(s.strip()) for s in value.split(',')]
	if missing_keys:
		warn(u"In entry {0}: missing key(s) {1!s}".format(entry, missing_keys))

	extraneous_keys = set(attributes.keys()) - processed_keys
	if extraneous_keys:
		warn(u"In entry {0}: unknown key(s) {1!s}. Have you misspelled them?".format(entry, list(extraneous_keys)))

	return sane_attributes

# reads the metadata file and returns a dict mapping each entry to the attributes
# specified. one can rely upon that they conform to the attribute_schema
def parse(filename):
	parser = ConfigParser.RawConfigParser(dict_type = OrderedDict)
	try:
		parser.readfp(codecs.open(filename, encoding='UTF-8', errors='strict'))
		return OrderedDict((sec, validate(sec, dict(parser.items(sec)))) for sec in parser.sections())
	except UnicodeDecodeError as ex:
		error(u"In file {0}: invalid UTF-8 character".format(filename), exception = ex, abort = True)

# reads the version file, composed of pairs of version number and release date
def read_versions(filename):
	versions = []
	try:
		with open(filename) as input:
			for line in input:
				try:
					version, release_date = line.split(" = ")
				except ValueError as ex:
					error(u"In file {0}: Malformed association {1}".format(filename, line), exception = ex)
					error("Not processing releases")
					return []
				else:
					versions.append((version, release_date.strip()))
	except Exception as ex:
		error(u"In file {0}: error".format(filename), exception = ex)
		error("Not processing releases")
		return []
	else:
		versions.sort(None, lambda (v, d): d, True)
		return versions

# reads the list of entry releases (metadata/releases)
def associate_releases(entries, versions, filename):
	for _, attributes in entries.items():
		attributes['releases'] = OrderedDict()
	prog = re.compile(release_pattern)
	warnings = {}
	try:
		with open(filename) as input:
			lines = []
			for line in input:
				line = line.strip()
				result = prog.match(line)
				try:
					entry, date = result.groups()
				except ValueError as ex:
					error(u"In file {0}: Malformed release {1}".format(filename, line.replace), exception = ex)
				else:
					if not entry in entries:
						if not entry in warnings:
							warnings[entry] = [line]
						else:
							warnings[entry].append(line)
					else:
						lines.append((entry, date))
		for entry, releases in warnings.items():
			warn(u"In file {0}: In release(s) {1!s}: Unknown entry {2}".format(filename, releases, entry))
		lines.sort(reverse = True)
		for line in lines:
			found = False
			entry, date = line
			for version_number, version_date in versions:
				if version_date <= date:
					entry_releases = entries[entry]['releases']
					if version_number not in entry_releases:
						entry_releases[version_number] = []
					entry_releases[version_number].append(date)
					found = True
					break
			if not found:
				warn(u"In file {0}: In release {1}: Release date {2} has no matching version".format(filename, line, date))
	except Exception as ex:
		error(u"In file {0}: error".format(filename), exception = ex)
		error("Not processing releases")
	finally:
		debug([(entry, attributes['releases']) for entry, attributes in entries.items()], title = "Releases")

def read_topics(filename):
	tree = Tree()
	stack = []
	with open(filename) as input:
		for line in input:
			count = 0
			while line[count] == ' ':
				count += 1
			if count % 2:
				raise Exception(u"Illegal indentation at line '{0}'".format(line))
			level = count // 2
			if level <= len(stack):
				stack = stack[0:level]
			else:
				raise Exception(u"Illegal indentation at line '{0}'".format(line))
			stack.append(line[count:len(line)-1])
			tree.add_topic(stack)
	return tree

# for topics page: group entries by topic
def collect_topics(entries):
	tree = read_topics(os.path.join(metadata_dir, "topics"))
	for entry, attributes in entries:
		for topic in attributes['topic']:
			tree.add_to_topic([str.strip() for str in topic.split('/')], entry)
	return tree

# for index page: group entries by year
def collect_years(entries):
	extracted = [
		(attributes['date'] if attributes['date'] != '' else 'unknown', entry, attributes)
		for entry, attributes in entries
	]
	extracted.sort(None, lambda (y, e, a): y, True)
	years = OrderedDict()
	for date, entry, attributes in extracted:
		key = date[0:4] if date != 'unknown' else date
		if key in years:
			years[key].append((entry, attributes))
		else:
			years[key] = [(entry, attributes)]
	return years.items()

def parse_extra(extra, **kwargs):
	k, v = extra.split(":", 1)
	return k.strip(), v.strip()

def parse_license(license, **kwargs):
	if license not in licenses:
		raise ValueError(u"Unknown license {0}".formate(license))
	return licenses[license]

# extracts name and URL from 'name <URL>' as a pair
def parse_author(author, entry, key):
	if author.find(" and ") != -1:
		warn(u"In entry {0}: {1} field contains 'and'. Use ',' to separate authors.".format(entry, key))
	url_start = author.find('<')
	url_end = author.find('>')
	if url_start != -1 and url_end != -1:
		url = author[url_start+1:url_end].strip()
		if url.startswith("mailto:"):
			url = url.replace("@", " /at/ ").replace(".", " /dot/ ")
		return author[:url_start].strip(), url
	else:
		notice(u"In entry {0}: no URL specified for {1} {2} ".format(entry, key, author))
		return author, None

# Extracts parts of a date, used in the bibtex files
def month_of_date(date):
	return "jan feb mar apr may jun jul aug sep oct nov dec".split(" ")[int(date.split("-")[1]) - 1]

def year_of_date(date):
	return date.split("-")[0]

# splits list of dependencies. returns empty list if no dependency is
# given
def parse_depends_on(dependency, **kwargs):
	deps = [x.strip() for x in dependency.split(',')]
	return filter(lambda x: x <> '', deps)

def generate_link_list(entries):
	return ''.join([html_topic_link.format(e) for e in entries])

# takes a list of author-URL pairs and formats a string, either with
# or without email addresses
def generate_author_list(authors, spacer, last_spacer, ignore_mail = True, ignore_url = False):
	def _to_str(author):
		name, url = author
		if url and not ignore_url:
			if url.startswith("mailto:"):
				if ignore_mail:
					return name
				else:
					return u"{0} ({1})".format(name, url[7:])
			return html_author_link.format(url, name)
		else:
			return name

	authors = map(_to_str, authors)
	if len(authors) == 0:
		return ""
	elif len(authors) == 1:
		return authors[0]
	else:
		return u"{0}{1}{2}".format(
	      spacer.join(authors[:len(authors)-1]),
		  last_spacer,
		  authors[len(authors)-1]
		)

# HTML formatting for topics page
def generate_topics(entries):
	def _gen(tree, level):
		result = ""
		if level <= html_until_level:
			if len(tree.entries) > 0:
				result += html_topic_link_list.format(generate_link_list(tree.entries))
			for topic, subtree in tree.subtopics.items():
				result += html_topic_headings[level].format(topic)
				if level < html_until_level:
					result += _gen(subtree, level + 1)
				else:
					result += html_topic_link_list.format(_gen(subtree, level + 1))
		else:
			result = generate_link_list(tree.entries)
			for topic, subtree in tree.subtopics.items():
				result += html_topic_headings[level].format(topic)
				result += _gen(subtree, level + 1)

		return result

	tree = collect_topics(entries)
	debug(tree, title = "Entries grouped by topic")
	return _gen(tree, 0)

# HTML formatting for index page
def generate_index(entries):
	years = collect_years(entries)
	debug(years, title = "Entries grouped by year")
	result = ""
	for year, list in years:
		rows = ""
		for entry, attributes in list:
			rows += html_index_entry.format(
				attributes['date'],
				entry,
				attributes['title'] if attributes['title'] != '' else entry,
				generate_author_list(attributes['author'], ",\n", " and \n")
			)
		result += html_index_year.format(year, rows)
	return result

def format_entry_text(title, text):
	return html_entry_text_wrapper.format(
		title, "\n" + text
	)

def format_entry_pre_text(title, text):
	return html_entry_pre_text_wrapper.format(
		title, text
	)

def depends_on_string(deps):
	return ', '.join(html_entry_link.format(dep, dep + ".shtml") for dep in deps)

def format_depends_on(deps):
	if len(deps) == 0:
		return ''
	else:
		return html_entry_depends_on_wrapper.format(depends_on_string(deps))

# HTML formatting for entry page
# supports the following parameters:
#   'header' for entry header (author, title, date etc.)
#   'older' for list of older releases
def generate_entry(entry, attributes, param):
	if param == "header":
		result = ""
		capitalized_title = ""
		for word in [str.strip() for str in attributes['title'].split(' ')]:
			if len(word) > 0 and word[0].isupper():
				capitalized_title += html_entry_capitalized.format(word[0], word[1:])
			else:
				capitalized_title += word + "\n"
		result += html_entry_heading.format(capitalized_title)

		text_columns = format_entry_text("Abstract", attributes['abstract'])
		text_columns += "".join([format_entry_text(k, v) for k, v in attributes['extra'].values()])
		text_columns += format_entry_pre_text("BibTeX",
			bibtex_wrapper.format(
				entry,
				generate_author_list(attributes['author'], ' and ', ' and ', ignore_url = True),
				attributes['title'],
				month_of_date(attributes['date']),
				year_of_date(attributes['date']))
		)

		result += html_entry_header_wrapper.format(
			attributes['title'],
			generate_author_list(attributes['author'], ', ', ' and ', ignore_mail = False),
			attributes['date'],
			text_columns,
			html_license_link.format(attributes['license'][0], attributes['license'][1]),
			entry,
			format_depends_on(attributes['depends-on']),
		)
	elif param == "older":
		if len(attributes['releases']) > 1:
			str = ""
			for version, release_dates in attributes['releases'].items()[1:]:
				str += "".join(html_entry_older_release.format(version, release_date) for release_date in release_dates)
			result = html_entry_older_list.format(str)
		else:
			result = "None"
	else:
		raise Exception("In generator 'entry': Unknown parameter "+param)

	return result

# look for templates in the metadata directory according to the definitions
# in the global configuration
def scan_templates(entries):
	for template in templates.keys():
		try:
			stats.tpls += 1
			template_filename = os.path.join(metadata_dir, template + template_suffix)
			if os.path.exists(template_filename):
				handle_template(entries, template, read_template(template_filename))
			else:
				raise(Exception("File not found. Make sure the files defined in 'templates' dict exist".format(template_filename)))
		except UnicodeDecodeError as ex:
			error(u"In file {0}: invalid UTF-8 character".format(template_filename), exception = ex)
			stats.failed_tpls += 1
			return
		except Exception as ex:
			error(u"In template {0}: File couldn't be processed".format(template_filename), exception = ex)
			stats.failed_tpls += 1
			return

# reads a template line by line and returns a list
# Suppose you have the following template content:
#   foo
#   bar
#   <!--gen-->
#   baz
#   <!--gen:param-->
#   qux
# then you will get the following result:
# [
#   (['foo', 'bar'], ''),
#   (['baz'], 'param'),
#   (['qux'], None)
# ]
def read_template(template_filename):
	lines = []
	result = []
	with codecs.open(template_filename, encoding='UTF-8', errors='strict') as input:
		debug(u"Reading template {0}".format(template_filename))
		found = False
		for line in input:
			stripped = line.strip()
			if stripped.startswith(magic_str_start) and stripped.endswith(magic_str_end):
				found = True

				param = stripped[len(magic_str_start):len(stripped)-len(magic_str_end)]
				if param.startswith(":"):
					param = param[1:].strip()
					debug(u"In file {0}: Found generator with parameter {1}".format(template_filename, param))
				else:
					debug(u"In file {0}: Found generator without parameter".format(template_filename))

				result.append((lines, param))
				lines = []
			else:
				lines.append(line)
		if not found:
			warn(u"In file {0}: No generator found".format(template_filename))

	result.append((lines, None))
	return result

# opens a file, invokes the generator and writes the result
def write_output(filename, content, generator):
	stats.gens += 1
	debug(u"Writing result to "+filename)
	failed = False
	try:
		with codecs.open(filename, mode='w', encoding='UTF-8', errors='strict') as output:
			for lines, param in content:
				for line in lines:
					output.write(line)
				if param != None:
					try:
						if param == '':
							result = generator()
						else:
							result = generator(param)
					except Exception as ex:
						failed = True

						error(u"For output file {0}: generator failed".format(filename), exception = ex)
					else:
						output.write(result)
	except Exception as ex:
		failed = True
		error(u"For output file {0}: error".format(filename), exception = ex)
	finally:
		if failed:
			stats.failed_gens += 1

# main function for handling a template
# Steps:
# * search the appropriate generator function
# * create destination directories
# * filter ignored entries
# * call write_output for each entry or for all entries together
def handle_template(entries, template, content):
	def _ignore(entry, attributes):
		if template in attributes['ignore']:
			notice(u"In template {0}: ignoring entry {1} because ignore flag is set in metadata".format(template, entry))
			return True
		else:
			return False

	dir, generator_str, for_each_func = templates[template]

	if generator_str not in globals():
		error(u"In template {0}: generator function {1} doesn't exist".format(template, generator_str))
		return
	else:
		generator = globals()[generator_str]

	dest_subdir = os.path.join(options.dest_dir, dir)
	try:
		os.makedirs(dest_subdir)
	except Exception as ex:
		if os.path.exists(dest_subdir):
			notice(u"In template {0}: directory {1} already existing".format(template, dest_subdir))
		else:
			error(u"In template {0}: directory {1} couldn't be created".format(template, dest_subdir), exception = ex)
			return

	not_ignored = [(entry, attributes) for entry, attributes in entries.items() if not _ignore(entry, attributes)]

	if for_each_func:
		for entry, attributes in not_ignored:
			output_filename = os.path.join(dest_subdir, for_each_func(entry) + output_suffix)
			write_output(output_filename, content, partial(generator, entry, attributes))
	else:
		output_filename = os.path.join(dest_subdir, template + output_suffix)
		write_output(output_filename, content, partial(generator, not_ignored))

# creates a makefile
def makefile(entries, dir):
	filename = os.path.join(dir, "IsaMakefile")
	try:
		with open(filename, "w") as output:
			output.write(".PHONY: all\n")
			output.write("all:")
			for k, _ in entries.items():
				output.write(" {0}".format(k))
			output.write("\n\n")
			for k, attributes in entries.items():
				output.write(".PHONY: {0}\n".format(k))
				output.write("{0}: {1}\n".format(k, " ".join(attributes["depends-on"])))
				output.write("\tmake -C {0} -f IsaMakefile all\n\n".format(k))
	except Exception as ex:
		failed = True
		error("Error writing Makefile {0}".format(filename), exception = ex)

# checks whether all dependencies are present
def check_deps(entries):
	keys = set(entries.keys())
	for key, attributes in entries.items():
		deps = set(attributes["depends-on"])
		if not deps.issubset(keys):
			warn(u"In entry {0}: Missing dependencies {1}".format(key, deps - keys))

if __name__ == "__main__":
	parser = OptionParser(usage = "Usage: %prog [--no-warn] [--debug] [--check=THYS_DIR | --dest=DEST_DIR | --makefile=THYS_DIR] metadata-dir")
	parser.add_option("--no-warn", action = "store_false", dest = "enable_warnings", default = True, help = "disable output of warnings")
	parser.add_option("--check", action = "store", type = "string", dest = "thys_dir", help = "compare the contents of the metadata file with actual file system contents")
	parser.add_option("--dest", action = "store", type = "string", dest = "dest_dir", help = "generate files for each template in the metadata directory")
	parser.add_option("--debug", action = "store_true", dest = "enable_debug", default = False, help = "display debug output")
	parser.add_option("--makefile", action = "store", type = "string", dest = "makefile_dir", help = "generate a makefile for building the whole AFP")

	(options, args) = parser.parse_args(argv)
	if len(args) != 2:
		parser.error("You must supply at least one parameter. For usage, supply --help.")
	if not options.thys_dir and not options.dest_dir and not options.makefile_dir:
		parser.error("You must supply at least one of --check or --dest or --makefile")

	metadata_dir = args[1]

	# parse metadata
	entries = parse(os.path.join(metadata_dir, "metadata"))
	versions = read_versions(os.path.join(metadata_dir, "release-dates"))
	associate_releases(entries, versions, os.path.join(metadata_dir, "releases"))
	debug(entries, title = "Entries from metadata file")
	if len(entries) == 0:
		warn("In metadata: No entries found")
	check_deps(entries)


	# perform check
	if options.thys_dir:
		count = check_fs(entries, options.thys_dir)
		output = "Checked directory {0}. Found {1} warnings.".format(options.thys_dir, count)
		color = 'yellow' if count > 0 else 'green'
		print(colored(output, color, attrs=['bold']))

	# perform generation
	if options.dest_dir:
		# parse template format
		magic_str_pos = magic_str.index("$")
		magic_str_start = magic_str[:magic_str_pos]
		magic_str_end = magic_str[magic_str_pos+1:]

		stats = Stats()
		scan_templates(entries)
		print(stats)

	if options.makefile_dir:
		makefile(entries, options.makefile_dir)
